include "cdir.mm"
include "wcel.mm"
include "cpw.mm"
include "ctail.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cmpt.mm"
include "wral.mm"
include "wss.mm"
include "cuni.mm"
include "crn.mm"
include "imassrn.mm"
include "cdm.mm"
include "cun.mm"
include "ssun2.mm"
include "dmrnssfld.mm"
include "sstri.mm"
include "dirdm.mm"
include "syl5req.mm"
include "syl5sseq.mm"
include "cvv.mm"
include "wb.mm"
include "dmexg.mm"
include "syl5eqel.mm"
include "elpw2g.mm"
include "syl.mm"
include "mpbird.mm"
include "ralrimivw.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylib.mm"
include "tailfval.mm"
include "feq1d.mm"

theorem tailf
  let cD: class D
  let cX: class X
  let vx: setvar x
  assume tailf.1: |- X = dom D


  assert |- ( D e. DirRel -> ( tail ` D ) : X --> ~P X )

  proof
    cD
    cdir
    wcel
    #
    cX
    cX
    cpw
    #
    cD
    ctail
    cfv
    #
    wf
    cX
    @1
    vx
    cX
    cD
    vx
    cv
    csn
    #
    cima
    #
    cmpt
    #
    wf
    #
    @0
    @4
    @1
    wcel
    #
    vx
    cX
    wral
    @6
    @0
    @7
    vx
    cX
    @0
    @7
    @4
    cX
    wss
    #
    @0
    cD
    cuni
    cuni
    #
    @4
    cX
    @4
    cD
    crn
    #
    @9
    cD
    @3
    imassrn
    @10
    cD
    cdm
    #
    @10
    cun
    @9
    @10
    @11
    ssun2
    cD
    dmrnssfld
    sstri
    sstri
    @0
    cX
    @11
    @9
    tailf.1
    cD
    dirdm
    syl5req
    syl5sseq
    @0
    cX
    cvv
    wcel
    @7
    @8
    wb
    @0
    cX
    @11
    cvv
    tailf.1
    cD
    cdir
    dmexg
    syl5eqel
    @4
    cX
    cvv
    elpw2g
    syl
    mpbird
    ralrimivw
    vx
    cX
    @1
    @4
    @5
    @5
    eqid
    fmpt
    sylib
    @0
    cX
    @1
    @2
    @5
    vx
    cD
    cX
    tailf.1
    tailfval
    feq1d
    mpbird
end
