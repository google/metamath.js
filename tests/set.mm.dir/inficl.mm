include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "wral.mm"
include "cfi.mm"
include "cfv.mm"
include "wceq.mm"
include "wss.mm"
include "ssfii.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "eqimss2.mm"
include "biantrurd.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "bitr3d.mm"
include "elabg.mm"
include "intss1.mm"
include "syl6bir.mm"
include "dffi2.mm"
include "sseq1d.mm"
include "sylibrd.mm"
include "eqss.mm"
include "simplbi2com.mm"
include "sylsyld.mm"
include "fiin.mm"
include "rgen2a.mm"
include "mpbii.mm"
include "impbid1.mm"

theorem inficl
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cV: class V
  let vt: setvar t
  let vz: setvar z
  let cB: class B

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint V y
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint V z
  assert |- ( A e. V -> ( A. x e. A A. y e. A ( x i^i y ) e. A <-> ( fi ` A ) = A ) )

  proof
    cA
    cV
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    cA
    wcel
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    cA
    cfi
    cfv
    #
    cA
    wceq
    #
    @0
    cA
    @7
    wss
    #
    @6
    @7
    cA
    wss
    #
    @8
    cA
    cV
    ssfii
    @0
    @6
    cA
    vz
    cv
    #
    wss
    #
    @3
    @11
    wcel
    #
    vy
    @11
    wral
    #
    vx
    @11
    wral
    #
    wa
    #
    vz
    cab
    #
    cint
    #
    cA
    wss
    #
    @10
    @0
    @6
    cA
    @17
    wcel
    @19
    @16
    @6
    vz
    cA
    cV
    @11
    cA
    wceq
    #
    @15
    @16
    @6
    @20
    @12
    @15
    cA
    @11
    eqimss2
    biantrurd
    @14
    @5
    vx
    @11
    cA
    @13
    @4
    vy
    @11
    cA
    @11
    cA
    @3
    eleq2
    raleqbi1dv
    raleqbi1dv
    bitr3d
    elabg
    cA
    @17
    intss1
    syl6bir
    @0
    @7
    @18
    cA
    vx
    vy
    vz
    cA
    cV
    dffi2
    sseq1d
    sylibrd
    @8
    @10
    @9
    @7
    cA
    eqss
    simplbi2com
    sylsyld
    @8
    @3
    @7
    wcel
    #
    vy
    @7
    wral
    #
    vx
    @7
    wral
    @6
    @21
    vx
    vy
    @7
    @1
    @2
    cA
    fiin
    rgen2a
    @22
    @5
    vx
    @7
    cA
    @21
    @4
    vy
    @7
    cA
    @7
    cA
    @3
    eleq2
    raleqbi1dv
    raleqbi1dv
    mpbii
    impbid1
end
