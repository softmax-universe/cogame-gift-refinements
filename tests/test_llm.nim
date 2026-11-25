import gift_refinements/prompts
## The decision layer (design note "## Tests" item 7).
##
## The tolerant extractor, the reply schema's repair-vs-reject split, the
## batched cadence, and the "never raises, always advances" contract of the
## fallback path. The transport is exercised through the real `decide.turn`
## with NO credentials, which is the same path certification runs.

import std/[json, monotimes, os, strutils, times]

import ./helpers
import curly
import gift_refinements/[decide, llm]

# These checks explicitly exercise the no-credentials fallback. A developer's
# shell must never turn them into provider-backed calls. Changes are process-local.
for key in ["COWORLD_LLM_ENDPOINT", "COWORLD_LLM_MODEL", "ANTHROPIC_API_KEY",
    "ANTHROPIC_API_KEY_URI", "AWS_ENDPOINT_URL_BEDROCK_RUNTIME", "AWS_BEARER_TOKEN_BEDROCK"]:
  delEnv(key)

suite "llm"

let aliases = @Aliases

block extractsBareAndSingleFencedObjectsOnly:
  let bare = """{"job":"hold","gift":0}"""
  check(extractJsonObject(bare){"job"}.getStr() == "hold",
    "a bare JSON object was not parsed")
  let fencedJson = "```json\n{\"job\":\"meet\",\"target\":\"Aro\",\"gift\":2}\n```"
  check(extractJsonObject(fencedJson){"job"}.getStr() == "meet",
    "a single ```json fenced object was not parsed")
  let fencedPlain = "```\n{\"job\":\"evade\"}\n```"
  check(extractJsonObject(fencedPlain){"job"}.getStr() == "evade",
    "a single plain ``` fenced object was not parsed")
  for bad in [
    "Sure! Here you go:\n```json\n{\"job\":\"meet\",\"target\":\"Aro\",\"gift\":2}\n```\nHope that helps.",
    "I think Cyr should hold. {\"job\":\"hold\",\"gift\":0} Done.",
    "{\"job\":\"hold\"} {\"job\":\"collect\"}",
    "```json\n{\"job\":\"hold\"}\n```\n```json\n{\"job\":\"collect\"}\n```",
    "```python\n{\"job\":\"hold\"}\n```",
    "no object here at all"
  ]:
    var raised = false
    try:
      discard extractJsonObject(bad)
    except OrderError:
      raised = true
    check(raised, "ambiguous or prose-wrapped reply was accepted: " & bad)
  banner "extractJsonObject accepts one bare or outer-fenced object and rejects prose/extra objects"

proc parses(payload: string, seat = 2): Order =
  parseOrder(extractJsonObject(payload), seat, aliases, DefaultMaxBeamsPerRound)

proc rejects(payload: string, why: string, seat = 2) =
  var raised = false
  try:
    discard parses(payload, seat)
  except OrderError:
    raised = true
  check(raised, why)

block schemaRejects:
  rejects("""{"job":"dance","target":null,"gift":0}""", "an unknown job was accepted")
  rejects("""{"target":"Aro","gift":1}""", "a reply with no job was accepted")
  rejects("""{"job":"meet","target":"Cyr","gift":1}""",
    "a cog was allowed to target itself")
  rejects("""{"job":"meet","target":"Zed","gift":1}""",
    "an unknown alias was accepted")
  rejects("""{"job":"meet","target":7,"gift":1}""",
    "a non-string target was accepted")
  rejects("""{"job":"collect","target":null,"gift":3}""",
    "gift > 0 with a null target was accepted")
  rejects("""{"job":"meet","target":null,"gift":0}""",
    "job meet with a null target was accepted")
  rejects("""{"job":"collect","gift":"lots"}""", "a non-integer gift was accepted")
  rejects("""{"job":"collect","gift":"2","target":"Aro"}""",
    "a string-encoded gift was accepted")
  rejects("""{"job":"collect","gift":1.0,"target":"Aro"}""",
    "a float-encoded gift was accepted")
  rejects("""{"job":"collect","gift":1.5,"target":"Aro"}""",
    "a fractional gift was accepted")
  rejects("""{"job":"meet","target":"Aro","gift":40}""",
    "an out-of-range gift > maxBeams was accepted")
  rejects("""{"job":"hold","gift":-1}""",
    "a negative gift was accepted")
  rejects("""{"job":"hold","consume":"maybe"}""", "an unknown consume was accepted")
  rejects("""{"job":"MEET","target":"Aro","gift":1}""",
    "a non-canonical job case was accepted")
  rejects("""{"job":" HOLD "}""", "a whitespace-padded job was accepted")
  rejects("""{"job":"meet","target":"aRo","gift":1}""",
    "a non-canonical alias case was accepted")
  rejects("""{"job":"hold","consume":"NEVER"}""",
    "a non-canonical consume case was accepted")
  rejects("""{"job":"hold","unknown_field":1}""",
    "an unexpected top-level field was accepted")
  rejects("""{"job":"hold","say":123}""",
    "a non-string say was accepted")
  rejects("""{"job":"hold","notes":[]}""",
    "a non-string notes was accepted")
  rejects("""{"job":"hold","say":"""" & "x".repeat(MaxSayRunes + 1) & """"}""",
    "an over-length say was accepted")
  rejects("""{"job":"hold","notes":"""" & "y".repeat(MaxNotesRunes + 1) & """"}""",
    "an over-length notes was accepted")
  banner "every invalid, coerced, out-of-range, legacy, or extra-field reply raises"

block schemaValidDefaultsAndExactFields:
  let zero = parses("""{"job":"meet","target":"Aro","gift":0}""")
  check(zero.gift == 0 and zero.target == 0 and not zero.clamped,
    "gift 0 with job meet and a valid target must be legal and unclamped")
  let defaults = parses("""{"job":"collect"}""")
  check(defaults.gift == 0, "an absent gift did not default to 0")
  check(defaults.consume == cwEnd, "an absent consume did not default to end")
  check(defaults.target == -1, "an absent target did not default to -1")
  check(defaults.say == "" and defaults.notes == "",
    "absent say/notes did not default to empty strings")
  let exact = parses("""{"job":"meet","target":"Aro","consume":"never","gift":1,"say":"hi","notes":"ok"}""")
  check(exact.job == jobMeet and exact.target == 0 and
        exact.consume == cwNever and exact.gift == 1 and
        exact.say == "hi" and exact.notes == "ok",
    "a complete exact order did not parse cleanly")
  let exactMax = parses("""{"job":"hold","say":"""" & "x".repeat(MaxSayRunes) &
    """","notes":"""" & "y".repeat(MaxNotesRunes) & """"}""")
  check(exactMax.say.len == MaxSayRunes and exactMax.notes.len == MaxNotesRunes,
    "exact max-length say/notes were modified")
  banner "genuine optional defaults and exact valid orders parse cleanly"

block maxTokensIsNamed:
  ## hanabi, 2026-08-24: a truncated reply used to surface as the misleading
  ## "unbalanced JSON object". The extractor raises it BY NAME instead.
  var config = defaultGameConfig()
  config.maxOutputTokens = 1000
  let client = newLlmClient(config)
  var response: Response
  response.code = 200
  response.body = """{"stop_reason":"max_tokens","content":[{"type":"text","text":"I will collect and then"}]}"""
  var message = ""
  try:
    discard client.textOf(response, "", "https://example.invalid")
  except LlmError as error:
    message = error.msg
  check("cut off at max_tokens" in message,
    "a max_tokens stop did not raise the named error, got: " & message)
  banner "a max_tokens stop before any '{' raises \"cut off at max_tokens\""

block transportFailuresNameThemselves:
  var config = defaultGameConfig()
  let client = newLlmClient(config)
  proc msgFor(code: int, body: string, transportError = ""): string =
    var response: Response
    response.code = code
    response.body = body
    try:
      discard client.textOf(response, transportError, "https://example.invalid")
    except LlmError as error:
      return error.msg
    ""
  check("throttled" in msgFor(429, "slow down"), "a 429 was not named a throttle")
  check("llm transport" in msgFor(0, "", "Timeout was reached"),
    "a transport error was not named")
  let auth = msgFor(403, "nope")
  check("auth failed" in auth, "a 403 was not named an auth failure")
  check(client.disabled,
    "a 403 must disable the client for the rest of the episode")
  banner "429 / transport / 401-403 each raise a named, rune-safe error"

block maxOutputTokensAndModelLadder:
  check(DefaultMaxOutputTokens >= 1000,
    "maxOutputTokens must be at least 1000 (hanabi, 2026-08-24)")
  let models = bedrockModelIds()
  check(models.len == 1, "the model ladder must have exactly one candidate")
  check("haiku" in models[0],
    "the only candidate must be haiku: every sonnet inference profile times " &
    "out on every sidecar call (raid, paintball)")
  banner "haiku-only ladder, maxOutputTokens >= 1000"

block wholeSecondDeadlines:
  ## curly floors CURLOPT_TIMEOUT to whole seconds, so a sub-second deadline is
  ## not the deadline it claims to be. sim_config REJECTS one.
  var config = defaultGameConfig()
  check(config.attempt1Ms mod 1000 == 0 and config.retryMs mod 1000 == 0,
    "the shipped deadlines are not whole seconds")
  check(config.attempt1Ms + config.retryMs <= config.turnBudgetMs,
    "the two attempts do not fit inside turnBudgetMs")
  config.attempt1Ms = 4500
  var raised = false
  try:
    config.validate()
  except GiftError:
    raised = true
  check(raised, "a sub-second attempt1Ms was accepted")
  config = defaultGameConfig()
  config.turnBudgetMs = 6000
  raised = false
  try:
    config.validate()
  except GiftError:
    raised = true
  check(raised, "attempt1Ms + retryMs > turnBudgetMs was accepted")
  banner "whole-second deadlines, and both attempts must fit the turn budget"

block requestRateStaysUnderThirtyPerMinute:
  ## The Bedrock sidecar caps 30 requests/minute PER EPISODE (raid,
  ## 2026-08-23). Worst case is six seats plus six retries per round, and the
  ## next batch cannot start before minTurnSeconds.
  let config = defaultGameConfig()
  let worstPerRound = SeatCount * 2
  let ratePerMinute = worstPerRound * 60 div max(1, config.minTurnSeconds)
  check(ratePerMinute < 30,
    "worst-case request rate is " & $ratePerMinute & "/min")
  let worstEpisodeSeconds =
    config.rounds * (config.turnBudgetMs div 1000) + 30 +
    config.shutdownGraceSeconds
  check(worstEpisodeSeconds <= config.playDeadlineSeconds(),
    "the worst-case episode is " & $worstEpisodeSeconds &
    " s against a play deadline of " & $config.playDeadlineSeconds() & " s")
  banner "worst case " & $ratePerMinute & " rpm and " & $worstEpisodeSeconds &
    " s, inside 30 rpm and " & $config.playDeadlineSeconds() & " s"

block lobbyStaysOpenUntilEverySeatIsIn:
  ## The lobby closes early ONLY with every declared seat connected AND
  ## registered. Closing as soon as the connected sockets had registered let
  ## the fast scripted filler pods close it while the champion pods were still
  ## dialling in, and those seats then played the scripted baseline for the
  ## whole episode (league rounds 2 and 4, 2026-08-26).
  let config = defaultGameConfig()
  check(config.numAgents == SeatCount, "the default config is not six seats")
  for connected in 1 ..< SeatCount:
    check(not config.lobbyShouldClose(connected, connected, 0),
      "the lobby closed at t=0 with only " & $connected & " seats in")
    check(not config.lobbyShouldClose(connected, connected, 5),
      "the lobby closed after 5 s with only " & $connected & " seats in")
    check(not config.lobbyShouldClose(
        connected, connected, config.playerConnectTimeoutSeconds - 1),
      "the lobby closed before the connect timeout with only " &
      $connected & " seats in")
  check(not config.lobbyShouldClose(SeatCount, SeatCount - 1, 10),
    "the lobby closed with a connected seat that had not registered")
  check(config.lobbyShouldClose(SeatCount, SeatCount, 0),
    "the lobby did not close with every seat connected and registered")
  check(config.lobbyShouldClose(0, 0, config.playerConnectTimeoutSeconds),
    "the lobby did not close at playerConnectTimeoutSeconds")
  check(config.lobbyShouldClose(
      3, 3, config.playerConnectTimeoutSeconds + 1),
    "a partly-filled lobby did not close after the connect timeout")
  banner "the lobby waits for every seat unless the connect timeout elapsed"

block oneBatchCarriesEveryOpenSeat:
  ## The batch is built ONE request per open seat, in one go. Building it here
  ## the same way `decide.turn` does is what makes "never sequentially"
  ## checkable without a network.
  var config = defaultGameConfig()
  let sim = initSimServer(config)
  let client = newLlmClient(config)
  let scene = sim.scene()
  var open: seq[int] = @[]
  for seat in 0 ..< SeatCount:
    open.add(seat)
  var batch: RequestBatch
  for seat in open:
    let view = sim.seatView(seat)
    let request = client.requestFor(
      systemPrompt(view, scene, PromptSelection()), userPrompt(view, scene, "be generous"), 0)
    batch.post(request.url, request.headers, request.body, $seat)
  check(batch.len == open.len,
    "the batch carries " & $batch.len & " requests for " & $open.len &
    " open seats")
  var retry: RequestBatch
  for seat in [1, 4]:
    let view = sim.seatView(seat)
    let request = client.requestFor(
      systemPrompt(view, scene, PromptSelection()), userPrompt(view, scene, ""), 0)
    retry.post(request.url, request.headers, request.body, $seat)
  check(retry.len == 2, "the retry batch must carry ONLY the failed seats")
  banner "one batch of six on round one; the retry batch carries only the failures"

block offlineTurnFallsBackWithoutRaising:
  ## With NO credentials the client disables itself instantly and every LLM
  ## seat plays the reciprocator order, marked `fallback`. This is the path
  ## offline certification and docker-smoke run, so it must be fast and silent.
  var config = defaultGameConfig()
  config.minTurnSeconds = 0
  var sim = initSimServer(config)
  var engine = initDecisionEngine(sim, PromptSelection())
  for seat in 0 ..< SeatCount:
    engine.seats[seat].registered = true
    if seat < 2:
      engine.seats[seat].isLlm = true
      engine.seats[seat].prompt = "be generous"
    else:
      engine.seats[seat].baseline =
        if seat mod 2 == 0: blReciprocator else: blHoarder
  let started = getMonoTime()
  let records = engine.turn(sim, 1, 0)
  let elapsed = (getMonoTime() - started).inMilliseconds.int
  check(elapsed < 2000,
    "an offline turn took " & $elapsed & " ms; it must not wait on a network")
  for seat in 0 ..< SeatCount:
    check(sim.haveOrder[seat], "seat " & $seat & " was left with no order")
  check(sim.orders[0].source == osFallback,
    "an LLM seat with no credentials was not marked source: fallback")
  check(sim.orders[0].job == jobHold and sim.orders[0].gift == 0 and
        sim.orders[0].consume == cwNever,
    "an LLM seat with no credentials did not fall back to neutral hold")
  check(sim.orders[2].source == osScripted,
    "a scripted seat was mis-marked as a fallback")
  var sawFallback = false
  for record in records:
    let node = parseJson(record)
    if node{"k"}.getStr() == "fallback":
      sawFallback = true
      check(node{"cause"}.getStr() == "no_credentials",
        "the fallback cause is " & node{"cause"}.getStr())
  check(sawFallback, "no fallback record was produced")
  # And the resulting orders are legal by the same validator the parser uses.
  for seat in 0 ..< SeatCount:
    let order = sim.orders[seat]
    check(order.gift >= 0 and order.gift <= config.maxBeamsPerRound,
      "a fallback order's gift is out of range")
    check(order.target != seat, "a fallback order targeted its own seat")
  banner "with no credentials LLM seats hold position and scripted seats run normally"

block repairMissingOrdersUsesHoldForLlmAndExternal:
  var config = defaultGameConfig()
  var sim = initSimServer(config)
  var engine = initDecisionEngine(sim, PromptSelection())
  engine.seats[0].isLlm = true
  engine.seats[1].isExternal = true
  for seat in 0 ..< SeatCount:
    sim.haveOrder[seat] = false
  engine.repairMissingOrders(sim)
  for seat in 0 ..< SeatCount:
    check(sim.haveOrder[seat], "seat " & $seat & " still has no order")
    check(sim.orders[seat].source == osFallback,
      "a repaired order is not marked as a fallback")
  check(sim.orders[0].job == jobHold and sim.orders[0].consume == cwNever,
    "missing LLM order did not use neutral hold")
  check(sim.orders[1].job == jobHold and sim.orders[1].consume == cwNever,
    "missing external order did not use neutral hold")
  banner "missing LLM/external orders use neutral hold; unregistered scripted seats use reciprocator"

block parseBaselineRejectsAliasesAndUnknowns:
  check(parseBaseline("") == blReciprocator, "empty baseline did not default to reciprocator")
  check(parseBaseline("reciprocator") == blReciprocator, "reciprocator did not parse")
  check(parseBaseline("hoarder") == blHoarder, "hoarder did not parse")
  for bad in ["hoard", "HOARDER", "leech", "unknown"]:
    var raised = false
    try:
      discard parseBaseline(bad)
    except ValueError:
      raised = true
    check(raised, "legacy or unknown baseline was accepted: " & bad)
  banner "parseBaseline accepts only empty/reciprocator/hoarder"

block promptsCarryTheContract:
  let sim = initSimServer(defaultGameConfig())
  let
    view = sim.seatView(2)
    scene = sim.scene()
    system = systemPrompt(view, scene, PromptSelection())
    user = userPrompt(view, scene, "open with the nearest cog")
  check("must begin with the character {" in system,
    "the system prompt does not demand a leading brace (Bedrock/Haiku answers " &
    "prose-first without it)")
  check("LOWEST held level" in system, "the gift rule is not stated as a rule")
  check("RAWEST FIRST" in system, "the rawest-first warning is missing")
  check("THE LADDER" in system, "the worked ladder is missing")
  check("NOBODY CAN HEAR ANYTHING YOU SAY" in system,
    "the prompt does not say there is no talk channel")
  check("CYR" in system, "the seat's own alias is not in capitals")
  for alias in ["Aro", "Bex", "Dov", "Eno", "Fay"]:
    check(alias in system, "the prompt does not name " & alias)
  check("open with the nearest cog" in user,
    "the operator block is missing from the user prompt")
  check("GUIDANCE FROM YOUR OPERATOR" in user,
    "the operator heading is missing")
  check("\"target\":\"Aro\"|" in user,
    "the user prompt does not precompute the legal target set")
  # NOTHING about the other seats' inventories, policies or the seed.
  for forbidden in ["policyNames", "gift-refinements-mirror", "seed"]:
    check(forbidden notin system and forbidden notin user,
      "the prompt leaks " & forbidden)
  banner "the prompts carry the output contract and leak nothing"

echo "test_llm OK"
