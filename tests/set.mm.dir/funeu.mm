include "wfun.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wex.mm"
include "weu.mm"
include "cdm.mm"
include "wcel.mm"
include "wrel.mm"
include "funrel.mm"
include "releldm.mm"
include "sylan.mm"
include "eldmg.mm"
include "ibi.mm"
include "syl.mm"
include "wmo.mm"
include "wi.mm"
include "funmo.mm"
include "adantr.mm"
include "df-mo.mm"
include "sylib.mm"
include "mpd.mm"

theorem funeu
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F

  disjoint A y
  disjoint F y
  assert |- ( ( Fun F /\ A F B ) -> E! y A F y )

  proof
    cF
    wfun
    #
    cA
    cB
    cF
    wbr
    #
    wa
    #
    cA
    vy
    cv
    cF
    wbr
    #
    vy
    wex
    #
    @3
    vy
    weu
    #
    @2
    cA
    cF
    cdm
    #
    wcel
    #
    @4
    @0
    cF
    wrel
    @1
    @7
    cF
    funrel
    cA
    cB
    cF
    releldm
    sylan
    @7
    @4
    vy
    cA
    cF
    @6
    eldmg
    ibi
    syl
    @2
    @3
    vy
    wmo
    #
    @4
    @5
    wi
    @0
    @8
    @1
    vy
    cA
    cF
    funmo
    adantr
    @3
    vy
    df-mo
    sylib
    mpd
end
