include "cc.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cmpt2.mm"
include "c1.mm"
include "cneg.mm"
include "cmul.mm"
include "caddc.mm"
include "cnsb.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "mulm1.mm"
include "adantl.mm"
include "oveq2d.mm"
include "negsub.mm"
include "eqtr2d.mm"
include "mpt2eq3ia.mm"
include "cxp.mm"
include "wfn.mm"
include "wf.mm"
include "subf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fnov.mm"
include "mpbi.mm"
include "cnv.mm"
include "cnnv.mm"
include "cnnvba.mm"
include "cnnvg.mm"
include "cnnvs.mm"
include "eqid.mm"
include "nvmfval.mm"
include "3eqtr4i.mm"

theorem cnnvm
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  assume cnnvm.6: |- U = <. <. + , x. >. , abs >.


  assert |- - = ( -v ` U )

  proof
    vx
    vy
    cc
    cc
    vx
    cv
    #
    vy
    cv
    #
    cmin
    co
    #
    cmpt2
    #
    vx
    vy
    cc
    cc
    @0
    c1
    cneg
    @1
    cmul
    co
    #
    caddc
    co
    #
    cmpt2
    #
    cmin
    cU
    cnsb
    cfv
    #
    vx
    vy
    cc
    cc
    @2
    @5
    @0
    cc
    wcel
    #
    @1
    cc
    wcel
    #
    wa
    #
    @5
    @0
    @1
    cneg
    #
    caddc
    co
    @2
    @10
    @4
    @11
    @0
    caddc
    @9
    @4
    @11
    wceq
    @8
    @1
    mulm1
    adantl
    oveq2d
    @0
    @1
    negsub
    eqtr2d
    mpt2eq3ia
    cmin
    cc
    cc
    cxp
    #
    wfn
    #
    cmin
    @3
    wceq
    @12
    cc
    cmin
    wf
    @13
    subf
    @12
    cc
    cmin
    ffn
    ax-mp
    vx
    vy
    cc
    cc
    cmin
    fnov
    mpbi
    cU
    cnv
    wcel
    @7
    @6
    wceq
    cU
    cnnvm.6
    cnnv
    vx
    vy
    cmul
    cU
    caddc
    @7
    cc
    cU
    cnnvm.6
    cnnvba
    cU
    cnnvm.6
    cnnvg
    cU
    cnnvm.6
    cnnvs
    @7
    eqid
    nvmfval
    ax-mp
    3eqtr4i
end
