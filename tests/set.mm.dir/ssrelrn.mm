include "cxp.mm"
include "wss.mm"
include "crn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "wrex.mm"
include "wi.mm"
include "elrng.mm"
include "ssbr.mm"
include "brxp.mm"
include "simplbi.mm"
include "syl6.mm"
include "ancrd.mm"
include "adantl.mm"
include "eximdv.mm"
include "ex.mm"
include "com23.mm"
include "sylbid.mm"
include "pm2.43i.mm"
include "impcom.mm"
include "df-rex.mm"
include "sylibr.mm"

theorem ssrelrn
  let cA: class A
  let cB: class B
  let cR: class R
  let cY: class Y
  let va: setvar a

  disjoint A a
  disjoint B a
  disjoint R a
  disjoint Y a
  assert |- ( ( R C_ ( A X. B ) /\ Y e. ran R ) -> E. a e. A a R Y )

  proof
    cR
    cA
    cB
    cxp
    #
    wss
    #
    cY
    cR
    crn
    #
    wcel
    #
    wa
    va
    cv
    #
    cA
    wcel
    #
    @4
    cY
    cR
    wbr
    #
    wa
    #
    va
    wex
    #
    @6
    va
    cA
    wrex
    @3
    @1
    @8
    @3
    @1
    @8
    wi
    #
    @3
    @3
    @6
    va
    wex
    #
    @9
    va
    cY
    cR
    @2
    elrng
    @3
    @1
    @10
    @8
    @3
    @1
    @10
    @8
    wi
    @3
    @1
    wa
    @6
    @7
    va
    @1
    @6
    @7
    wi
    @3
    @1
    @6
    @5
    @1
    @6
    @4
    cY
    @0
    wbr
    #
    @5
    cR
    @0
    @4
    cY
    ssbr
    @11
    @5
    cY
    cB
    wcel
    @4
    cY
    cA
    cB
    brxp
    simplbi
    syl6
    ancrd
    adantl
    eximdv
    ex
    com23
    sylbid
    pm2.43i
    impcom
    @6
    va
    cA
    df-rex
    sylibr
end
