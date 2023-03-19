include "caa.mm"
include "wcel.mm"
include "cmpaa.mm"
include "cfv.mm"
include "cv.mm"
include "cdgr.mm"
include "cdgraa.mm"
include "wceq.mm"
include "cc0.mm"
include "ccoe.mm"
include "c1.mm"
include "w3a.mm"
include "cq.mm"
include "cply.mm"
include "crab.mm"
include "wa.mm"
include "crio.mm"
include "mpaaval.mm"
include "wreu.mm"
include "mpaaeu.mm"
include "riotacl2.mm"
include "syl.mm"
include "eqeltrd.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "fveq1.mm"
include "fveq1d.mm"
include "3anbi123d.mm"
include "elrab.mm"
include "sylib.mm"

theorem mpaalem
  let cA: class A
  let vd: setvar d
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cP: class P


  assert |- ( A e. AA -> ( ( minPolyAA ` A ) e. ( Poly ` QQ ) /\ ( ( deg ` ( minPolyAA ` A ) ) = ( degAA ` A ) /\ ( ( minPolyAA ` A ) ` A ) = 0 /\ ( ( coeff ` ( minPolyAA ` A ) ) ` ( degAA ` A ) ) = 1 ) ) )

  proof
    cA
    caa
    wcel
    #
    cA
    cmpaa
    cfv
    #
    vp
    cv
    #
    cdgr
    cfv
    #
    cA
    cdgraa
    cfv
    #
    wceq
    #
    cA
    @2
    cfv
    #
    cc0
    wceq
    #
    @4
    @2
    ccoe
    cfv
    #
    cfv
    #
    c1
    wceq
    #
    w3a
    #
    vp
    cq
    cply
    cfv
    #
    crab
    #
    wcel
    @1
    @12
    wcel
    @1
    cdgr
    cfv
    #
    @4
    wceq
    #
    cA
    @1
    cfv
    #
    cc0
    wceq
    #
    @4
    @1
    ccoe
    cfv
    #
    cfv
    #
    c1
    wceq
    #
    w3a
    #
    wa
    @0
    @1
    @11
    vp
    @12
    crio
    #
    @13
    cA
    vp
    mpaaval
    @0
    @11
    vp
    @12
    wreu
    @22
    @13
    wcel
    cA
    vp
    mpaaeu
    @11
    vp
    @12
    riotacl2
    syl
    eqeltrd
    @11
    @21
    vp
    @1
    @12
    @2
    @1
    wceq
    #
    @5
    @15
    @7
    @17
    @10
    @20
    @23
    @3
    @14
    @4
    @2
    @1
    cdgr
    fveq2
    eqeq1d
    @23
    @6
    @16
    cc0
    cA
    @2
    @1
    fveq1
    eqeq1d
    @23
    @9
    @19
    c1
    @23
    @4
    @8
    @18
    @2
    @1
    ccoe
    fveq2
    fveq1d
    eqeq1d
    3anbi123d
    elrab
    sylib
end
