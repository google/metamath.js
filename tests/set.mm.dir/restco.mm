include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cin.mm"
include "cmpt.mm"
include "crn.mm"
include "crest.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "vex.mm"
include "inex1.mm"
include "ineq1.mm"
include "inass.mm"
include "syl6eq.mm"
include "abrexco.mm"
include "eqid.mm"
include "rnmpt.mm"
include "mpteq1.mm"
include "ax-mp.mm"
include "3eqtr4i.mm"
include "restval.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "cvv.mm"
include "ovex.mm"
include "syl6eqelr.mm"
include "simp3.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "simp1.mm"
include "inex1g.mm"
include "3ad2ant2.mm"
include "3eqtr4a.mm"

theorem restco
  let cA: class A
  let cB: class B
  let cJ: class J
  let cV: class V
  let cW: class W
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( J e. V /\ A e. W /\ B e. X ) -> ( ( J |`t A ) |`t B ) = ( J |`t ( A i^i B ) ) )

  proof
    cJ
    cV
    wcel
    #
    cA
    cW
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    vx
    vy
    cJ
    vy
    cv
    #
    cA
    cin
    #
    cmpt
    #
    crn
    #
    vx
    cv
    #
    cB
    cin
    #
    cmpt
    #
    crn
    #
    vy
    cJ
    @4
    cA
    cB
    cin
    #
    cin
    #
    cmpt
    #
    crn
    #
    cJ
    cA
    crest
    co
    #
    cB
    crest
    co
    #
    cJ
    @12
    crest
    co
    #
    vz
    cv
    #
    @9
    wceq
    vx
    vw
    cv
    @5
    wceq
    vy
    cJ
    wrex
    vw
    cab
    #
    wrex
    vz
    cab
    @19
    @13
    wceq
    vy
    cJ
    wrex
    vz
    cab
    @11
    @15
    vz
    vx
    vw
    vy
    cJ
    @5
    @9
    @13
    @4
    cA
    vy
    vex
    inex1
    @8
    @5
    wceq
    @9
    @5
    cB
    cin
    @13
    @8
    @5
    cB
    ineq1
    @4
    cA
    cB
    inass
    syl6eq
    abrexco
    vx
    vz
    @20
    @9
    @10
    @7
    @20
    wceq
    @10
    vx
    @20
    @9
    cmpt
    wceq
    vy
    vw
    cJ
    @5
    @6
    @6
    eqid
    rnmpt
    vx
    @7
    @20
    @9
    mpteq1
    ax-mp
    rnmpt
    vy
    vz
    cJ
    @13
    @14
    @14
    eqid
    rnmpt
    3eqtr4i
    @3
    @17
    @7
    cB
    crest
    co
    #
    @11
    @3
    @16
    @7
    cB
    crest
    @0
    @1
    @16
    @7
    wceq
    @2
    vy
    cA
    cJ
    cV
    cW
    restval
    3adant3
    #
    oveq1d
    @3
    @7
    cvv
    wcel
    @2
    @21
    @11
    wceq
    @3
    @7
    @16
    cvv
    @22
    cJ
    cA
    crest
    ovex
    syl6eqelr
    @0
    @1
    @2
    simp3
    vx
    cB
    @7
    cvv
    cX
    restval
    syl2anc
    eqtrd
    @3
    @0
    @12
    cvv
    wcel
    #
    @18
    @15
    wceq
    @0
    @1
    @2
    simp1
    @1
    @0
    @23
    @2
    cA
    cB
    cW
    inex1g
    3ad2ant2
    vy
    @12
    cJ
    cV
    cvv
    restval
    syl2anc
    3eqtr4a
end
