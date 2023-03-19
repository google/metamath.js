include "cnp.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cltq.mm"
include "wbr.mm"
include "wrex.mm"
include "cplq.mm"
include "co.mm"
include "wex.mm"
include "prnmax.mm"
include "wceq.mm"
include "cnq.mm"
include "ltrelnq.mm"
include "brel.mm"
include "simprd.mm"
include "ltexnq.mm"
include "biimpcd.mm"
include "mpd.mm"
include "eleq1a.mm"
include "eximdv.mm"
include "syl5.mm"
include "rexlimiv.mm"
include "syl.mm"

theorem prnmadd
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( ( A e. P. /\ B e. A ) -> E. x ( B +Q x ) e. A )

  proof
    cA
    cnp
    wcel
    cB
    cA
    wcel
    wa
    cB
    vy
    cv
    #
    cltq
    wbr
    #
    vy
    cA
    wrex
    cB
    vx
    cv
    cplq
    co
    #
    cA
    wcel
    #
    vx
    wex
    #
    vy
    cA
    cB
    prnmax
    @1
    @4
    vy
    cA
    @1
    @2
    @0
    wceq
    #
    vx
    wex
    #
    @0
    cA
    wcel
    #
    @4
    @1
    @0
    cnq
    wcel
    #
    @6
    @1
    cB
    cnq
    wcel
    @8
    cB
    @0
    cnq
    cnq
    cltq
    ltrelnq
    brel
    simprd
    @8
    @1
    @6
    vx
    cB
    @0
    ltexnq
    biimpcd
    mpd
    @7
    @5
    @3
    vx
    @0
    cA
    @2
    eleq1a
    eximdv
    syl5
    rexlimiv
    syl
end
