include "cnv.mm"
include "wcel.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "cneg.mm"
include "cns.mm"
include "cfv.mm"
include "co.mm"
include "cpv.mm"
include "cmpt2.mm"
include "wral.mm"
include "wa.mm"
include "simpl.mm"
include "simprl.mm"
include "cc.mm"
include "neg1cn.mm"
include "eqid.mm"
include "nvscl.mm"
include "mp3an2.mm"
include "adantrl.mm"
include "nvgcl.mm"
include "syl3anc.mm"
include "ralrimivva.mm"
include "fmpt2.mm"
include "sylib.mm"
include "nvmfval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem nvmf
  let cU: class U
  let cM: class M
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume nvmf.1: |- X = ( BaseSet ` U )
  assume nvmf.3: |- M = ( -v ` U )


  assert |- ( U e. NrmCVec -> M : ( X X. X ) --> X )

  proof
    cU
    cnv
    wcel
    #
    cX
    cX
    cxp
    #
    cX
    cM
    wf
    @1
    cX
    vx
    vy
    cX
    cX
    vx
    cv
    #
    c1
    cneg
    #
    vy
    cv
    #
    cU
    cns
    cfv
    #
    co
    #
    cU
    cpv
    cfv
    #
    co
    #
    cmpt2
    #
    wf
    #
    @0
    @8
    cX
    wcel
    #
    vy
    cX
    wral
    vx
    cX
    wral
    @10
    @0
    @11
    vx
    vy
    cX
    cX
    @0
    @2
    cX
    wcel
    #
    @4
    cX
    wcel
    #
    wa
    #
    wa
    @0
    @12
    @6
    cX
    wcel
    #
    @11
    @0
    @14
    simpl
    @0
    @12
    @13
    simprl
    @0
    @13
    @15
    @12
    @0
    @3
    cc
    wcel
    @13
    @15
    neg1cn
    @3
    @4
    @5
    cU
    cX
    nvmf.1
    @5
    eqid
    #
    nvscl
    mp3an2
    adantrl
    @2
    @6
    cU
    @7
    cX
    nvmf.1
    @7
    eqid
    #
    nvgcl
    syl3anc
    ralrimivva
    vx
    vy
    cX
    cX
    @8
    cX
    @9
    @9
    eqid
    fmpt2
    sylib
    @0
    @1
    cX
    cM
    @9
    vx
    vy
    @5
    cU
    @7
    cM
    cX
    nvmf.1
    @17
    @16
    nvmf.3
    nvmfval
    feq1d
    mpbird
end
