include "crngo.mm"
include "wcel.mm"
include "crnghom.mm"
include "co.mm"
include "w3a.mm"
include "cghomOLD.mm"
include "crn.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "eqid.mm"
include "rngohomf.mm"
include "wa.mm"
include "rngohomadd.mm"
include "eqcomd.mm"
include "ralrimivva.mm"
include "wb.mm"
include "cgr.mm"
include "rngogrpo.mm"
include "elghomOLD.mm"
include "syl2an.mm"
include "3adant3.mm"
include "mpbir2and.mm"

theorem rngogrphom
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cJ: class J
  let vx: setvar x
  let vy: setvar y
  assume rnggrphom.1: |- G = ( 1st ` R )
  assume rnggrphom.2: |- J = ( 1st ` S )


  assert |- ( ( R e. RingOps /\ S e. RingOps /\ F e. ( R RngHom S ) ) -> F e. ( G GrpOpHom J ) )

  proof
    cR
    crngo
    wcel
    #
    cS
    crngo
    wcel
    #
    cF
    cR
    cS
    crnghom
    co
    wcel
    #
    w3a
    #
    cF
    cG
    cJ
    cghomOLD
    co
    wcel
    #
    cG
    crn
    #
    cJ
    crn
    #
    cF
    wf
    #
    vx
    cv
    #
    cF
    cfv
    vy
    cv
    #
    cF
    cfv
    cJ
    co
    #
    @8
    @9
    cG
    co
    cF
    cfv
    #
    wceq
    #
    vy
    @5
    wral
    vx
    @5
    wral
    #
    cR
    cS
    cF
    cG
    cJ
    @5
    @6
    rnggrphom.1
    @5
    eqid
    #
    rnggrphom.2
    @6
    eqid
    #
    rngohomf
    @3
    @12
    vx
    vy
    @5
    @5
    @3
    @8
    @5
    wcel
    @9
    @5
    wcel
    wa
    wa
    @11
    @10
    @8
    @9
    cR
    cS
    cF
    cG
    cJ
    @5
    rnggrphom.1
    @14
    rnggrphom.2
    rngohomadd
    eqcomd
    ralrimivva
    @0
    @1
    @4
    @7
    @13
    wa
    wb
    #
    @2
    @0
    cG
    cgr
    wcel
    cJ
    cgr
    wcel
    @16
    @1
    cR
    cG
    rnggrphom.1
    rngogrpo
    cS
    cJ
    rnggrphom.2
    rngogrpo
    vx
    vy
    cF
    cG
    cJ
    @6
    @5
    @14
    @15
    elghomOLD
    syl2an
    3adant3
    mpbir2and
end
