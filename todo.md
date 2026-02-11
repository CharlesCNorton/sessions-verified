# sessions-verified — Implementation Plan

## Global Policy

P1. Use `Defined` (not `Qed`) for every lemma in the transitive dependency chain of any extracted function, starting from Layer 0. Do not defer this to hardening — retrofitting `Defined` over `Qed` deep in the proof tree is painful and error-prone.

P2. Use half-open intervals `[start, end)` throughout, with membership defined as `start <= t < end`. Do NOT mix with closed intervals `[start, end]`. Half-open intervals partition cleanly without shared-endpoint special cases. The interval sigma type (item 6) must use `iv_start < iv_end` (strict), and membership must be `iv_start <= t < iv_end`.

P3. All timestamps are POSIX time (no leap seconds). The system assumes input timestamps count SI seconds since 1970-01-01T00:00:00Z with no leap-second insertions, matching exchange timestamp conventions. Document this assumption explicitly in the formalization header and README. No leap-second table is needed.

P4. Microsecond precision is a deliberate design constraint. Some exchanges (NYSE, CME) now timestamp in nanoseconds. Document that the system truncates to microsecond resolution and that nanosecond-precision inputs must be pre-rounded by the caller. If parameterizing precision later, the duration/instant types already support it since Z is unbounded — the microsecond constant (1000000 per second) would become a parameter.

## Layer 0: Foundations (Z-based time arithmetic)

1. Use `Z` (binary integers) throughout, not `nat`. Import `ZArith`, `Lia`. Set extraction to `ExtrOcamlZInt` so Z maps to OCaml `int` with no unary penalty.
2. Define `instant : Type := Z` as signed microseconds since the Unix epoch (1970-01-01T00:00:00Z). Prove `instant` has decidable equality and a total order via `Z.compare`.
3. Define `duration : Type := Z` as signed microseconds. Prove `duration` forms an abelian group under addition. Prove `instant + duration = instant` and `instant - instant = duration` with the expected cancellation laws.
4. Define `ceil_div_Z` and `floor_div_Z` for Z with explicit rounding-direction proofs. Prove `floor_div_Z a b * b <= a < floor_div_Z a b * b + b` for `b > 0`. Prove `ceil_div_Z a b * b >= a > ceil_div_Z a b * b - b` for `b > 0`. These are the workhorses for bar alignment.
5. Prove that `Z.compare` on instants is reflexive, antisymmetric, and transitive as standalone lemmas (not relying on lia inside later proofs).
6. Define `interval := { iv_start : instant ; iv_end : instant ; iv_wf : iv_start < iv_end }` as a sigma type with **strict** inequality (nondegenerate). Membership is half-open: `iv_start <= t < iv_end`. Prove decidable membership, decidable overlap, decidable containment, and decidable disjointness. (See policy P2.)
7. Prove interval arithmetic: `iv_duration iv = iv_end iv - iv_start iv > 0`. Prove that splitting an interval at a point `t` inside it (`iv_start < t < iv_end`) yields two valid intervals whose durations sum to the original.
8. Define `covers (intervals : list interval) (outer : interval) : Prop` asserting that every instant `t` with `iv_start outer <= t < iv_end outer` belongs to at least one interval in the list. Define `partitions (intervals : list interval) (outer : interval) : Prop` asserting `covers` plus pairwise disjointness. These are the central structural predicates — bars must partition sessions, sessions must partition trading days.

## Layer 1: Gregorian Calendar

9. Define `year`, `month` (1–12), `day` (1–31), `hour` (0–23), `minute` (0–59), `second` (0–59), `microsecond` (0–999999) as Z-valued types with range predicates.
10. Define `is_leap_year (y : Z) : bool` implementing the 400/100/4 rule. Prove `is_leap_year 2000 = true`, `is_leap_year 1900 = false`, `is_leap_year 2024 = true`, `is_leap_year 2023 = false` by computation.
11. Define `days_in_month (y : Z) (m : Z) : Z` returning 28/29/30/31. Prove it is always in `{28, 29, 30, 31}`. Prove `days_in_month y 2 = 29 <-> is_leap_year y = true`.
12. Define `days_in_year (y : Z) : Z` as the sum of `days_in_month` over 12 months. Prove `days_in_year y = 365 + (if is_leap_year y then 1 else 0)`.
13. Define `valid_date (y m d : Z) : Prop := 1 <= m <= 12 /\ 1 <= d <= days_in_month y m`. Prove decidability.
14. Define `date_to_epoch_days (y m d : Z) : Z` mapping a Gregorian date to days since 1970-01-01. Use Howard Hinnant's `days_from_civil` algorithm. Prove correctness for all valid Gregorian dates (the algorithm is correct for all Z, not just the C++ chrono range of -32768..32767 — prove it without artificial range bounds). Prove injectivity: `date_to_epoch_days y1 m1 d1 = date_to_epoch_days y2 m2 d2 -> (y1,m1,d1) = (y2,m2,d2)` for valid dates.
15. Define `epoch_days_to_date (days : Z) : Z * Z * Z` as the inverse. Prove `epoch_days_to_date (date_to_epoch_days y m d) = (y, m, d)` for all valid dates. Prove `date_to_epoch_days (epoch_days_to_date d) = d` (where the triple is destructured). This round-trip pair is the calendar kernel — every later layer depends on it.
16. Define `datetime_to_instant (y m d h min s us : Z) : instant` composing date-to-epoch-days with time-of-day arithmetic: `date_to_epoch_days y m d * 86400000000 + h * 3600000000 + min * 60000000 + s * 1000000 + us`. Prove this is strictly monotone in the lexicographic order of `(y, m, d, h, min, s, us)`.
17. Define `instant_to_datetime (t : instant) : Z * Z * Z * Z * Z * Z * Z` as the inverse. Prove the full round-trip in both directions.
18. Define `day_of_week (y m d : Z) : Z` (0 = Monday, 6 = Sunday) using Tomohiko Sakamoto's algorithm or equivalent. Prove `day_of_week` is consistent with `date_to_epoch_days`: `day_of_week y m d = (date_to_epoch_days y m d + 3) mod 7` (since 1970-01-01 was a Thursday = day 3). Prove the range is always 0–6.

## Layer 2: Time Zones and DST

19. Define `utc_offset : Type := Z` as signed minutes from UTC (e.g., EST = -300, JST = +540). Prove that applying an offset and its negation is the identity: `t + offset * 60000000 - offset * 60000000 = t`.
20. Define a `tz_transition` record: `{ tt_at : instant ; tt_offset_before : utc_offset ; tt_offset_after : utc_offset }`. This is a single DST or zone-rule change at a specific UTC instant. `tt_at` is the exact UTC microsecond when the new offset takes effect. Note: this also handles permanent zone changes (e.g., Russia 2014, Samoa 2011) — they're just transitions with no periodic pattern.
21. Define `tz_rule : Type := list tz_transition` as a sorted (by `tt_at`) list of transitions. Define `tz_rule_sorted (r : tz_rule) : Prop` and `tz_rule_no_dup (r : tz_rule) : Prop` (no two transitions at the same instant). Bundle these into a `well_formed_tz_rule` record.
22. Define `utc_to_offset (r : tz_rule) (t : instant) : utc_offset` returning the active offset at UTC instant `t`. This is a pure lookup: find the last transition at or before `t`, return its `tt_offset_after`; if `t` precedes all transitions, return the `tt_offset_before` of the first transition. Prove this function is total — it returns a definite offset for every instant, with no option type.
23. Define `utc_to_local (r : tz_rule) (t : instant) : instant := t + utc_to_offset r t * 60000000`. Prove this is total.
24. Prove that `utc_to_local` is monotone within any contiguous offset interval (between consecutive transitions), but NOT globally monotone — demonstrate a counterexample at a fall-back transition where two distinct UTC instants map to the same local instant.
25. Define the DST gap predicate: `is_gap (r : tz_rule) (local_t : instant) : Prop` — a local time that corresponds to no UTC instant. This occurs during spring-forward: the local clock jumps from `tt_at + offset_before` to `tt_at + offset_after`, and times between those two local instants don't exist. Prove that gaps occur iff `tt_offset_after > tt_offset_before` for some transition.
26. Define the DST overlap predicate: `is_overlap (r : tz_rule) (local_t : instant) : Prop` — a local time that corresponds to two distinct UTC instants. This occurs during fall-back. Prove overlaps occur iff `tt_offset_after < tt_offset_before`.
27. Define `local_to_utc (r : tz_rule) (local_t : instant) : instant` as the *total* inverse of `utc_to_local`. For gaps, snap forward to the first valid local instant after the gap. For overlaps, choose the *later* UTC instant (i.e., prefer the new offset). Document and prove both choices. Prove `local_to_utc r (utc_to_local r t) = t` for all `t` (the round-trip from UTC is exact). Prove that `utc_to_local r (local_to_utc r lt) = lt` when `lt` is not in a gap.
28. Prove the gap/overlap classification theorem: for every local instant `lt` and well-formed tz_rule `r`, exactly one of three cases holds: (a) `lt` is in a gap, (b) `lt` is in an overlap, (c) `lt` corresponds to exactly one UTC instant. This is the totality-of-classification theorem.
29. Encode concrete tz_rules for at least: `America/New_York` (EST/EDT), `America/Chicago` (CST/CDT), `Europe/London` (GMT/BST), `Asia/Tokyo` (JST, no DST), `Asia/Hong_Kong` (HKT, no DST), `Australia/Sydney` (AEST/AEDT, southern hemisphere DST). Include transitions for at least 2020–2030. Prove each is `well_formed_tz_rule`.
30. Validate encoded transitions against IANA tzdata. Write an OCaml test (Layer 8) that compares `utc_to_offset` output at every encoded transition instant against a known-good reference (e.g., Python `zoneinfo` or the IANA tz database directly). A single wrong transition microsecond silently corrupts every downstream result.

## Layer 3: Holiday Calendars

31. Define `holiday_calendar : Type := list (Z * Z * Z)` as a sorted list of `(year, month, day)` triples. Define `well_formed_calendar` requiring sorted order, valid dates, and no duplicates.
32. Define `is_holiday (cal : holiday_calendar) (y m d : Z) : bool` by linear scan on the sorted list. (Note: Coq `list` does not support O(log n) random access, so "binary search" on a list is still O(n). Accept O(n) here — holiday calendars are ~250 entries per decade per exchange. The extracted OCaml can use an array or set for production performance if needed, justified by correctness equivalence at the boundary.) Prove decidability and correctness: `is_holiday cal y m d = true <-> In (y, m, d) cal`.
33. Define `is_weekend (y m d : Z) : bool := day_of_week y m d >=? 5`. Prove correctness.
34. Define `is_business_day (cal : holiday_calendar) (y m d : Z) : bool := negb (is_weekend y m d) && negb (is_holiday cal y m d)`. Prove decidability.
35. Define `next_business_day` and `prev_business_day` that skip weekends and holidays. Prove unconditional termination by bounding the search to 366 days and proving that a business day must exist within any 10-day window given the weekend structure (at most 2 weekend days per 7, so any 10-day window contains at least 6 weekdays; even if 5 are holidays, one remains). Do NOT use the "holidays don't span more than 5 consecutive weekdays" hypothesis — it fails for TSE (6+ weekday closures around New Year) and HKEX (full-week Chinese New Year closures). Prove `next_business_day` returns a strictly later date. Prove `prev_business_day` returns a strictly earlier date.
36. Define `count_business_days (cal : holiday_calendar) (start_date end_date : Z * Z * Z) : Z`. Prove it equals the cardinality of `{d | start_date <= d <= end_date /\ is_business_day cal d = true}`. Prove monotonicity: extending the range cannot decrease the count.
37. Encode concrete holiday calendars for at least: NYSE, NASDAQ, CME, LSE, TSE (Tokyo), HKEX, ASX. Include holidays for 2020–2030. For each, prove `well_formed_calendar`.
38. Define holiday observation rules: `observed_holiday` handling Saturday→Friday and Sunday→Monday shifts for US markets. Prove that observed holidays are valid dates and that the observation function is idempotent.

## Layer 4: Trading Sessions

39. Define `session_template` as one of two forms: **intraday** (open < close, both offsets from midnight local time) or **overnight** (open > close, meaning the session starts on day D at the open offset and ends on day D+1 at the close offset). The intraday form carries `st_open_offset < st_close_offset`. The overnight form carries `st_open_offset > st_close_offset` and computes duration as `(24h - open) + close`. This is required for CME futures (e.g., ES: 18:00 ET → 17:00 ET next day), SGX, and any exchange with sessions crossing midnight.

40. Define `early_close_template` record: same as `session_template` but with close earlier than the regular close. Carry a proof that the early close is between open and regular close. For overnight sessions, "earlier close" means a shorter session — the close offset is still on day D+1 but at an earlier time.

41. Define `intraday_sessions : Type := list session_template` as a list of non-overlapping, sorted intraday sub-sessions for exchanges with mid-day breaks. TSE has morning (9:00–11:30) and afternoon (12:30–15:00) sessions. The well-formedness condition requires: (a) each sub-session is intraday (not overnight); (b) sub-sessions are sorted by open offset; (c) consecutive sub-sessions are disjoint (`close_i <= open_{i+1}`). When a trading calendar uses `intraday_sessions`, `session_for_date` returns the *union* of sub-session intervals for the date.

42. Define `trading_calendar` record bundling: `{ tc_tz : tz_rule ; tc_holidays : holiday_calendar ; tc_regular : session_template OR intraday_sessions ; tc_early_closes : list (Z * Z * Z * early_close_template) ; tc_pre_market : option session_template ; tc_after_hours : option session_template ; tc_late_opens : list (Z * Z * Z * duration) }`. The `tc_late_opens` field handles delayed openings (weather, technical issues) by overriding the open offset for specific dates.

43. Define `session_for_date (tc : trading_calendar) (y m d : Z) : option (list interval)`. Returns `None` if the date is a weekend or holiday. Returns `Some ivs` where `ivs` is a list of UTC intervals computed by converting local open/close times through `local_to_utc` using `tc_tz`. For single-session exchanges this is a one-element list. For TSE-style exchanges with mid-day breaks, it is a multi-element list. If the date appears in `tc_early_closes`, use the early close time. If the date appears in `tc_late_opens`, use the late open time. Prove: when the result is `Some ivs`, every interval in `ivs` is nondegenerate, and the intervals are pairwise disjoint and sorted.

44. Prove totality of session classification: for every UTC instant `t`, define `session_status (tc : trading_calendar) (t : instant)` returning one of: `InRegularSession date sub_session_index`, `InPreMarket date`, `InAfterHours date`, `Closed`. Prove this classification is total — every instant gets exactly one status. Prove decidability. Document that this reflects the *scheduled* state — unscheduled closures (trading halts, circuit breakers, emergency closures) are out of scope and must be handled by an unverified layer.

45. Prove session non-overlap: for a well-formed `trading_calendar`, no two sessions (regular sub-sessions, pre-market, after-hours) for any date overlap with each other or with sessions of adjacent dates. This requires proving that the after-hours session ends before the next day's pre-market session begins. For overnight sessions, prove that the session ending on day D+1 does not overlap with day D+1's regular session. State the required separation hypotheses explicitly.

46. Prove that consecutive regular sessions for consecutive business days have a positive gap between them (closed period exists). For overnight sessions, prove this means the maintenance break between close and next open is positive. Prove the closed period duration is always at least the expected gap minus any DST shift.

47. Prove DST-session interaction theorems: (a) a spring-forward during a session shortens it by the gap duration; (b) a fall-back during a session lengthens it by the overlap duration; (c) if a spring-forward gap contains the local open time, the session starts at the first valid local instant after the gap (inherited from `local_to_utc` behavior). Prove that in all three cases every session sub-interval is still nondegenerate.

48. Define `sessions_in_range (tc : trading_calendar) (start end_ : instant) : list (Z * Z * Z * list interval)` returning all `(year, month, day, session_intervals)` tuples whose session intersects `[start, end_)`. Prove: (a) the returned list is sorted by first session start; (b) all session intervals (across all dates) are pairwise disjoint; (c) every returned interval intersects `[start, end_)`; (d) no session intersecting `[start, end_)` is omitted.

## Layer 5: Bar and Window Bucketing

49. Define `bar_width : Type := { bw_us : Z ; bw_pos : bw_us > 0 }`. Common widths: 1-second (1000000), 1-minute (60000000), 5-minute (300000000), 15-minute, 30-minute, 1-hour, 4-hour, 1-day.

50. Define `bar_index (bw : bar_width) (session_start : instant) (t : instant) : Z := floor_div_Z (t - session_start) (bw_us bw)`. This assigns every instant within a session to a bar number. Prove: `bar_index` is monotone (later instants get equal or higher index). Prove: two instants in the same bar have `|t1 - t2| < bw_us bw`.

51. Define `bar_interval (bw : bar_width) (session_start : instant) (idx : Z) : interval` returning the half-open interval `[session_start + idx * bw_us, session_start + (idx + 1) * bw_us)`. Prove: `bar_interval` produces a valid interval (start < end). Prove: `t` falls in `bar_interval bw session_start (bar_index bw session_start t)` for all `t >= session_start`.

52. Prove the bar partition theorem: for a session sub-interval `[open, close)` and bar width `bw`, the bars `bar_interval bw open 0`, `bar_interval bw open 1`, ..., `bar_interval bw open (n-1)` partition the session, where `n = ceil_div_Z (close - open) (bw_us bw)`. Prove: (a) every instant in `[open, close)` falls in exactly one bar; (b) bars are pairwise disjoint; (c) bars are contiguous (bar k's end = bar k+1's start); (d) the first bar starts at `open`; (e) the last bar ends at or after `close`. For exchanges with mid-day breaks, bars are computed per sub-session — bar indices reset at each sub-session boundary.

53. Prove the partial-bar theorem: if `(close - open)` is not divisible by `bw_us bw`, the last bar extends past `close`. Compute the partial bar's effective duration as `(close - open) mod (bw_us bw)`. Prove this is strictly between 0 and `bw_us bw`. Define `bar_count` as `ceil_div_Z (close - open) (bw_us bw)` and prove it equals the number of bars covering the session.

54. Define `session_bar_index (tc : trading_calendar) (bw : bar_width) (t : instant) : option (Z * Z * Z * Z * Z)` returning `Some (year, month, day, sub_session_index, bar_idx)` if `t` is in a regular session, `None` otherwise. Prove totality of the composed classification: every instant either gets a `(date, sub_session, bar)` or is confirmed out-of-session.

55. Define `bar_boundaries (tc : trading_calendar) (bw : bar_width) (y m d : Z) : list (list instant)` returning bar-boundary instants for each sub-session on the given date. Prove: (a) each sub-list is sorted; (b) the first element of each sub-list equals the sub-session open; (c) consecutive elements differ by exactly `bw_us bw` except possibly the last pair; (d) the last element of each sub-list equals or exceeds the sub-session close.

56. Prove cross-session bar independence: bars from different sessions (including different sub-sessions of different dates) never share an instant. This follows from session non-overlap (item 45) but state and prove it as a standalone corollary.

57. Define multi-day bar aggregation: `daily_bar (tc : trading_calendar) (y m d : Z)` as the list of bars spanning each sub-session entirely. For single-session exchanges, this is one bar with `bw_us = close - open`. For multi-session exchanges, this is one bar per sub-session. Prove each daily bar count is 1 per sub-session.

58. Define `vwap_window (tc : trading_calendar) (t : instant) (lookback : duration) : option interval` returning `Some [max(sub_session_open, t - lookback), t)` clipped to the current sub-session, or `None` if `t` is not in a session. Prove: (a) when `Some`, the result is a valid interval; (b) it is contained within the current sub-session; (c) its duration is `min(lookback, t - sub_session_open)`.

59. Define `weekly_bars (tc : trading_calendar) (bw : bar_width) (y m d : Z) : list interval` aggregating bars across all sessions in the Monday–Friday week containing the given date. Prove the result is a sorted list of disjoint intervals. Note: weekly and monthly bars span multiple sessions and are computed as the *union* of per-session bar lists, not as a single continuous interval. Multi-session bar aggregation is inherently a list operation, not a single-interval operation.

## Layer 6: Parameterization and Abstraction

60. Wrap Layers 0–5 in a parameterized `Section` over the `trading_calendar`. All theorems should hold for any well-formed calendar, not just the hardcoded exchange instances.

61. Define a `well_formed_trading_calendar` record bundling all required hypotheses: tz_rule sorted and no-dup, holiday calendar sorted and valid, session templates valid, early closes are subsets of business days, late opens are subsets of business days, pre-market ends before regular open, after-hours starts after regular close, overnight sessions don't overlap next day's regular session, intraday sub-sessions are disjoint and sorted, etc. Prove that each concrete exchange instance satisfies `well_formed_trading_calendar`.

62. Define an abstract `exchange` Module Type exposing: `tz_rule`, `holiday_calendar`, `session_template` (or `intraday_sessions`), `early_close_template`, plus all well-formedness proofs. Provide concrete Module implementations for NYSE, NASDAQ, CME, LSE, TSE, HKEX, ASX.

## Layer 7: Extraction and OCaml Interface

63. Add `Require Import Extraction`, `ExtrOcamlBasic`, `ExtrOcamlZInt`. Extract all of: `utc_to_local`, `local_to_utc`, `utc_to_offset`, `session_for_date`, `session_status`, `bar_index`, `bar_interval`, `bar_count`, `bar_boundaries`, `session_bar_index`, `sessions_in_range`, `daily_bar`, `vwap_window`, `is_business_day`, `next_business_day`, `prev_business_day`, `count_business_days`, `instant_to_datetime`, `datetime_to_instant`, `day_of_week`, `detect_gaps` (for DST gap detection).

64. Verify that NO extracted function returns an `option` for a query that the formalization proves total. The extracted type signatures must reflect totality: `session_status` returns a sum type with no `None` branch, `bar_index` returns `Z`, `utc_to_offset` returns `Z`. Any extracted `option` must correspond to a genuinely partial operation (e.g., `session_for_date` on a holiday).

65. Write a hand-crafted `.mli` hiding extraction internals (Z representation, positives, etc.), exposing only the public API with OCaml-native types (`int` for microsecond instants, `int` for offsets, etc.).

66. Write an OCaml functor `Session_functor.Make(E : EXCHANGE)` wrapping the extracted functions. `EXCHANGE` provides: `tz_transitions`, `holidays`, `session_open`, `session_close`, `early_closes`, `late_opens`, `intraday_sessions`. The functor instantiates the parameterized Coq code.

67. Add `validate` at the functor boundary rejecting instants outside the supported transition range (e.g., before 2020 or after 2030 if only those transitions are encoded) and rejecting years outside the holiday calendar range. Raise `Invalid_argument` with a descriptive message.

## Layer 8: Tests

68. Write round-trip unit tests for `datetime_to_instant` / `instant_to_datetime` covering: epoch (1970-01-01T00:00:00Z), leap day (2024-02-29), end of year (2023-12-31T23:59:59.999999Z), negative years, dates before/after epoch.

69. Write DST transition tests for `America/New_York`: (a) spring-forward 2024-03-10T02:00 EST → 03:00 EDT, verify the gap is detected, verify `local_to_utc` snaps forward; (b) fall-back 2024-11-03T02:00 EDT → 01:00 EST, verify the overlap is detected, verify `local_to_utc` picks the later UTC instant.

70. Write session tests for NYSE: (a) regular session 2024-01-02 (first trading day of year) opens 9:30 ET, closes 16:00 ET, verify UTC intervals; (b) early close 2024-07-03 (day before July 4th) closes 13:00 ET; (c) holiday 2024-07-04 returns no session; (d) weekend 2024-01-06 (Saturday) returns no session.

71. Write session tests for TSE: (a) verify morning session 9:00–11:30 JST and afternoon session 12:30–15:00 JST are returned as two disjoint intervals; (b) verify bar indices reset between morning and afternoon sub-sessions; (c) verify a mid-day timestamp (12:00 JST) is classified as `Closed`.

72. Write session tests for CME ES futures: (a) verify overnight session 18:00 ET → 17:00 ET next day spans two calendar dates; (b) verify the 17:00–18:00 maintenance break is classified as `Closed`; (c) verify DST transitions during overnight sessions produce nondegenerate intervals.

73. Write bar bucketing tests: (a) 1-minute bars on a 6.5-hour NYSE session yield exactly 390 bars; (b) 5-minute bars yield 78 bars; (c) bar 0 starts at 9:30, bar 1 starts at 9:31 (for 1-min bars); (d) the last bar's effective end equals 16:00.

74. Write a DST-session interaction test: pick a date where spring-forward occurs during pre-market hours (e.g., 2024-03-10 for NYSE). Verify the pre-market session is shortened. Verify the regular session is unaffected. Verify bar counts adjust.

75. Write a random stress test (1000+ trials): generate random UTC instants in [2020, 2030), classify via `session_status`, verify the classification is consistent with `session_for_date` for the same date, verify bar indices are non-negative and bounded by `bar_count`.

76. Write a property test: for 1000 random business days across all 7 exchanges, verify that `sessions_in_range` over a 24-hour window centered on noon returns exactly one session (or zero for holidays), that each session sub-interval is nondegenerate, and that bar boundaries partition it.

77. Write an exhaustive DST-boundary test: for every transition in every encoded tz_rule (2020–2030), generate instants at `transition - 1us`, `transition`, and `transition + 1us`, verify `utc_to_offset` returns the correct offset at each, and verify `utc_to_local` produces the expected local time.

78. Write a tz_rule validation test: for every encoded transition in every tz_rule, compare `utc_to_offset` output against a known-good reference (IANA tzdata via Python `zoneinfo` or equivalent). This catches data-entry errors in the hardcoded transition instants.

## Layer 9: Hardening

79. Prove that all `Fixpoint` and `Function` definitions used in extraction pass Coq's guard checker on structural arguments (no fuel parameters, no `Program Fixpoint` with opaque obligations). Every recursive function must have a structurally decreasing argument visible in the type.

80. Prove that `bar_index` never produces a negative index for `t >= session_start`. Prove that `bar_index` never exceeds `bar_count - 1` for `t < session_close`.

81. Prove the microsecond-precision round-trip: `instant_to_datetime (datetime_to_instant y m d h min s us) = (y, m, d, h, min, s, us)` for all valid 7-tuples, and the converse. This is the ultimate test of the calendar kernel — no off-by-one, no rounding, no truncation.

82. Prove that `utc_to_offset` is piecewise constant: it changes value only at transition instants. Formally: if `t1 < t2` and there is no transition `tt_at` with `t1 < tt_at <= t2`, then `utc_to_offset r t1 = utc_to_offset r t2`.

83. Prove that `sessions_in_range` is idempotent under re-query: querying the range `[min(starts), max(ends))` of the returned sessions returns the same list.

84. Prove that `local_to_utc` composed with `utc_to_local` is the identity: `local_to_utc r (utc_to_local r t) = t` for all `t`. Prove separately that `utc_to_local r (local_to_utc r lt) = lt` when `lt` is not in a DST gap, and characterize the snap behavior when it is.

85. Prove that the total ordering on instants is preserved through bar indexing: if `t1 < t2` and both are in the same sub-session, then `bar_index bw open t1 <= bar_index bw open t2`. Prove strict inequality iff `t1` and `t2` are in different bars.

86. Verify the `Defined`/`Qed` policy (P1): audit every lemma in the transitive closure of extracted functions and confirm none uses `Qed`. This is a check, not a retrofit — the policy should have been followed from item 1.

## Layer 10: Documentation and Build

87. Write a `README.md` with: problem statement (why market time is hard), trust boundary table (verified vs. unverified), proven properties table with theorem names, event model, API reference, building instructions. Document: POSIX time assumption (no leap seconds), microsecond precision constraint, overnight session support, mid-day break support, and the explicit out-of-scope items (unscheduled closures, trading halts, circuit breakers, auction phases).

88. Write a `USAGE.md` with functor instantiation example, API table with complexity annotations, and trust boundary explanation.

89. Write a `Makefile` with targets: `extract` (coqc → .ml), `test` (OCaml unit tests), `test-random` (property tests), `test-dst` (DST boundary tests), `test-tz-validation` (compare against IANA tzdata), `bench` (throughput benchmark for bar classification), `clean`, `all`.

90. Add a `.gitignore` excluding: `*.vo`, `*.vos`, `*.vok`, `*.glob`, `*.aux`, `.lia.cache`, `*.cmo`, `*.cmi`, `*.exe`, `build/`, `_build/`, `*.byte`, `*.native`.

91. Ensure the final line count of `sessions.v` is documented in the README. Target: the formalization should be self-contained in a single `.v` file (no Coq library dependencies beyond the standard library and ZArith).

## Acknowledged Limitations

L1. **Auction phases** (opening auction, closing auction, intraday auctions) are not modeled. The session status reflects continuous trading only. An unverified layer may subdivide sessions into auction and continuous phases if needed.

L2. **Unscheduled closures** (trading halts, circuit breakers, emergency closures like 9/11 or Hurricane Sandy) cannot be predicted and are not in any calendar. `session_status` reflects the *scheduled* state. Real-time halt detection must be handled by an unverified layer consuming exchange halt messages.

L3. **Nanosecond precision** is not natively supported. The system uses microsecond resolution (see policy P4). Nanosecond timestamps must be pre-rounded by the caller.

L4. **Multi-session bar aggregation** (weekly bars, monthly bars) is provided as a list of per-session bar lists, not as a single continuous bar. This is inherent to the domain — there is no single interval spanning a week of trading that doesn't include closed periods.
