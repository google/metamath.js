include "cgr.mm"
include "wcel.mm"
include "cghomOLD.mm"
include "co.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "crn.mm"
include "wf.mm"
include "eqid.mm"
include "elghomOLD.mm"
include "biimp3a.mm"
include "simprd.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "mpan9.mm"

theorem ghomlinOLD
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume ghomlinOLD.1: |- X = ran G


  assert |- ( ( ( G e. GrpOp /\ H e. GrpOp /\ F e. ( G GrpOpHom H ) ) /\ ( A e. X /\ B e. X ) ) -> ( ( F ` A ) H ( F ` B ) ) = ( F ` ( A G B ) ) )

  proof
    cG
    cgr
    wcel
    #
    cH
    cgr
    wcel
    #
    cF
    cG
    cH
    cghomOLD
    co
    wcel
    #
    w3a
    #
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    cH
    co
    #
    @4
    @6
    cG
    co
    #
    cF
    cfv
    #
    wceq
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    cA
    cX
    wcel
    cB
    cX
    wcel
    wa
    cA
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    cH
    co
    #
    cA
    cB
    cG
    co
    #
    cF
    cfv
    #
    wceq
    #
    @3
    cX
    cH
    crn
    #
    cF
    wf
    #
    @12
    @0
    @1
    @2
    @20
    @12
    wa
    vx
    vy
    cF
    cG
    cH
    @19
    cX
    ghomlinOLD.1
    @19
    eqid
    elghomOLD
    biimp3a
    simprd
    @11
    @18
    @13
    @7
    cH
    co
    #
    cA
    @6
    cG
    co
    #
    cF
    cfv
    #
    wceq
    vx
    vy
    cA
    cB
    cX
    cX
    @4
    cA
    wceq
    #
    @8
    @21
    @10
    @23
    @24
    @5
    @13
    @7
    cH
    @4
    cA
    cF
    fveq2
    oveq1d
    @24
    @9
    @22
    cF
    @4
    cA
    @6
    cG
    oveq1
    fveq2d
    eqeq12d
    @6
    cB
    wceq
    #
    @21
    @15
    @23
    @17
    @25
    @7
    @14
    @13
    cH
    @6
    cB
    cF
    fveq2
    oveq2d
    @25
    @22
    @16
    cF
    @6
    cB
    cA
    cG
    oveq2
    fveq2d
    eqeq12d
    rspc2v
    mpan9
end
