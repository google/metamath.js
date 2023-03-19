include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cen.mm"
include "wbr.mm"
include "cardid2.mm"
include "ensymd.mm"
include "breq2.mm"
include "en0.mm"
include "syl6bb.mm"
include "syl5ibcom.mm"
include "fveq2.mm"
include "card0.mm"
include "syl6eq.mm"
include "impbid1.mm"

theorem cardnueq0
  let cA: class A
  let vx: setvar x


  assert |- ( A e. dom card -> ( ( card ` A ) = (/) <-> A = (/) ) )

  proof
    cA
    ccrd
    cdm
    wcel
    #
    cA
    ccrd
    cfv
    #
    c0
    wceq
    #
    cA
    c0
    wceq
    #
    @0
    cA
    @1
    cen
    wbr
    #
    @2
    @3
    @0
    @1
    cA
    cA
    cardid2
    ensymd
    @2
    @4
    cA
    c0
    cen
    wbr
    @3
    @1
    c0
    cA
    cen
    breq2
    cA
    en0
    syl6bb
    syl5ibcom
    @3
    @1
    c0
    ccrd
    cfv
    c0
    cA
    c0
    ccrd
    fveq2
    card0
    syl6eq
    impbid1
end
