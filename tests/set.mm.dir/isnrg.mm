include "cv.mm"
include "cnm.mm"
include "cfv.mm"
include "cabv.mm"
include "wcel.mm"
include "cngp.mm"
include "cnrg.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eleq12d.mm"
include "df-nrg.mm"
include "elrab2.mm"

theorem isnrg
  let cA: class A
  let cR: class R
  let cN: class N
  let vr: setvar r
  assume isnrg.1: |- N = ( norm ` R )
  assume isnrg.2: |- A = ( AbsVal ` R )


  assert |- ( R e. NrmRing <-> ( R e. NrmGrp /\ N e. A ) )

  proof
    vr
    cv
    #
    cnm
    cfv
    #
    @0
    cabv
    cfv
    #
    wcel
    cN
    cA
    wcel
    vr
    cR
    cngp
    cnrg
    @0
    cR
    wceq
    #
    @1
    cN
    @2
    cA
    @3
    @1
    cR
    cnm
    cfv
    cN
    @0
    cR
    cnm
    fveq2
    isnrg.1
    syl6eqr
    @3
    @2
    cR
    cabv
    cfv
    cA
    @0
    cR
    cabv
    fveq2
    isnrg.2
    syl6eqr
    eleq12d
    vr
    df-nrg
    elrab2
end
