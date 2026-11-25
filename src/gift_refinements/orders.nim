## The standing-order schema: what a policy (LLM, external, or scripted) may say
## and how replies are strictly validated.
##
## Forked from `coworld-ctf/src/ctf/directives.nim`. All policy kinds emit the
## SAME object, so one validator covers all of them -- that is what makes the
## bounded-orders test in `tests/test_baseline.nim` meaningful.
##
## RUNE DISCIPLINE (see sim_types.cleanText): every cap here is in runes.

import std/[json, strutils, unicode]

import ./sim_types

type
  Job* = enum
    jobCollect = "collect"
    jobMeet = "meet"
    jobHold = "hold"
    jobEvade = "evade"

  ConsumeWhen* = enum
    cwNow = "now"
    cwEnd = "end"
    cwNever = "never"

  OrderSource* = enum
    osLlm = "llm"
    osFallback = "fallback"
    osScripted = "scripted"
    osExternal = "external"

  Order* = object
    ## One seat's whole decision for one round (60 ticks). A deterministic
    ## kernel turns this into that round's per-tick action stream.
    job*: Job
    target*: int               ## slot, or -1 for none
    gift*: int                 ## 0 .. maxBeamsPerRound
    consume*: ConsumeWhen
    say*: string               ## <= MaxSayRunes; SPECTATOR-ONLY, never
                               ## delivered to another seat
    notes*: string             ## <= MaxNotesRunes; private to this seat
    clamped*: bool
    source*: OrderSource
    latencyMs*: int

  OrderError* = object of ValueError
    ## An INVALID REPLY: rejected strictly so invalid orders fail unscored.

proc defaultOrder*(): Order =
  Order(job: jobCollect, target: -1, gift: 0, consume: cwEnd, source: osScripted)

const AllowedOrderFields = ["job", "target", "gift", "consume", "say", "notes"]

proc stripOuterJsonFence*(text: string): string =
  ## Unwraps a single ordinary outer Markdown code fence (plain or `json`)
  ## when present. Leaves bare text untouched. Raises OrderError on malformed
  ## or non-JSON outer fences.
  result = text.strip()
  if not result.startsWith("```"):
    return result
  let newline = result.find('\n')
  if newline < 0:
    raise newException(OrderError, "unterminated markdown fence in reply")
  let tag = result[3 ..< newline].strip().toLowerAscii()
  if tag.len > 0 and tag != "json":
    raise newException(OrderError,
      "unsupported markdown fence tag: " & tag.cleanText(40))
  var inner = result[newline + 1 .. ^1]
  if not inner.endsWith("```"):
    raise newException(OrderError, "unterminated markdown fence in reply")
  inner = inner[0 ..< inner.len - 3]
  let lastNl = inner.rfind('\n')
  if lastNl >= 0:
    if inner[lastNl + 1 .. ^1].strip().len > 0:
      raise newException(OrderError, "malformed closing markdown fence in reply")
  elif inner.strip().len > 0:
    raise newException(OrderError, "malformed closing markdown fence in reply")
  result = inner.strip()

proc extractJsonObject*(text: string): JsonNode =
  ## Extracts exactly one JSON object, bare or inside a single ordinary outer
  ## Markdown code fence (JSON-tagged or plain). Rejects surrounding prose,
  ## extra objects, and non-object JSON values.
  let body = stripOuterJsonFence(text)
  if body.len == 0 or body[0] != '{' or body[^1] != '}':
    var head = text.strip()
    if head.runeLen > 160:
      head = head.truncateRunes(160) & "\u2026"
    raise newException(
      OrderError, "reply must be one JSON object: " & head.replace("\n", " "))
  try:
    result = parseJson(body)
  except CatchableError as error:
    raise newException(OrderError, "invalid JSON object: " & error.msg)
  if result.isNil or result.kind != JObject:
    raise newException(OrderError, "reply is not a JSON object")

proc parseJob(text: string): tuple[ok: bool, job: Job] =
  for job in Job:
    if $job == text:
      return (true, job)
  (false, jobCollect)

proc parseConsumeWhen(text: string): tuple[ok: bool, value: ConsumeWhen] =
  for value in ConsumeWhen:
    if $value == text:
      return (true, value)
  (false, cwEnd)

proc aliasSlot*(aliases: openArray[string], text: string): int =
  ## Exact alias lookup. Returns -1 when nothing matches.
  if text.len == 0:
    return -1
  for slot, alias in aliases:
    if alias == text:
      return slot
  -1

proc parseOrder*(
  payload: JsonNode, seat: int, aliases: openArray[string], maxBeams: int
): Order =
  ## Strictly validates one parsed reply into a legal order.
  ##
  ## OPTIONAL DEFAULTS:
  ##   * an absent or null `gift` defaults to 0;
  ##   * an absent or null `consume` defaults to `end`;
  ##   * an absent or null `target` defaults to none (when allowed);
  ##   * an absent or null `say` / `notes` defaults to "".
  ##
  ## REJECTED (raises OrderError):
  ##   * unexpected top-level keys;
  ##   * `job` missing or not an exact enum string;
  ##   * `gift` not an integer or outside 0..maxBeams;
  ##   * `target` not an exact other-cog alias string or null, or targeting self,
  ##     or absent/null when `job == meet` or `gift > 0`;
  ##   * `consume` not an exact enum string or null;
  ##   * `say` / `notes` not strings (when present and non-null) or exceeding
  ##     their rune limits.
  result = defaultOrder()
  result.source = osLlm
  if payload.isNil or payload.kind != JObject:
    raise newException(OrderError, "reply is not a JSON object")

  for key in payload.keys:
    if key notin AllowedOrderFields:
      raise newException(OrderError,
        "unexpected order field: " & key.cleanText(40))

  let jobNode = payload{"job"}
  if jobNode.isNil or jobNode.kind != JString:
    raise newException(OrderError, "reply has no \"job\" string")
  let job = parseJob(jobNode.getStr())
  if not job.ok:
    raise newException(OrderError,
      "unknown job " & jobNode.getStr().cleanText(40) &
      " (expected collect|meet|hold|evade)")
  result.job = job.job

  # --- gift -----------------------------------------------------------------
  let giftNode = payload{"gift"}
  var gift = 0
  if not giftNode.isNil and giftNode.kind != JNull:
    if giftNode.kind != JInt:
      raise newException(OrderError, "gift must be an integer")
    let rawGift = giftNode.getBiggestInt()
    if rawGift < 0 or rawGift > maxBeams:
      raise newException(OrderError,
        "gift out of range 0.." & $maxBeams & ": " & $rawGift)
    gift = int(rawGift)
  result.gift = gift

  # --- target ---------------------------------------------------------------
  let targetNode = payload{"target"}
  var target = -1
  if not targetNode.isNil and targetNode.kind != JNull:
    if targetNode.kind != JString:
      raise newException(OrderError, "target must be an alias string or null")
    target = aliasSlot(aliases, targetNode.getStr())
    if target < 0:
      raise newException(OrderError,
        "unknown target alias " & targetNode.getStr().cleanText(40))
    if target == seat:
      raise newException(OrderError, "a cog cannot target itself")
  if target < 0 and (result.job == jobMeet or result.gift > 0):
    raise newException(OrderError,
      "target is required when job is meet or gift > 0")
  result.target = target

  # --- consume --------------------------------------------------------------
  let consumeNode = payload{"consume"}
  if not consumeNode.isNil and consumeNode.kind != JNull:
    if consumeNode.kind != JString:
      raise newException(OrderError, "consume must be now|end|never")
    let parsed = parseConsumeWhen(consumeNode.getStr())
    if not parsed.ok:
      raise newException(OrderError,
        "unknown consume " & consumeNode.getStr().cleanText(40) &
        " (expected now|end|never)")
    result.consume = parsed.value

  # --- say & notes ----------------------------------------------------------
  let sayNode = payload{"say"}
  if not sayNode.isNil and sayNode.kind != JNull:
    if sayNode.kind != JString:
      raise newException(OrderError, "say must be a string or null")
    result.say = sayNode.getStr().truncateRunes(MaxSayRunes)

  let notesNode = payload{"notes"}
  if not notesNode.isNil and notesNode.kind != JNull:
    if notesNode.kind != JString:
      raise newException(OrderError, "notes must be a string or null")
    result.notes = notesNode.getStr().truncateRunes(MaxNotesRunes)

proc targetAlias*(order: Order, aliases: openArray[string]): string =
  if order.target < 0 or order.target >= aliases.len: "" else: aliases[order.target]

proc orderJson*(order: Order, aliases: openArray[string]): JsonNode =
  %*{"job": $order.job,
    "target": (if order.target < 0: newJNull() else: %aliases[order.target]),
    "gift": order.gift, "consume": $order.consume,
    "say": order.say, "notes": order.notes}
