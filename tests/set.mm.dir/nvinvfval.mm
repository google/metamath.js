include "cnv.mm"
include "wcel.mm"
include "cba.mm"
include "cfv.mm"
include "cgn.mm"
include "wf.mm"
include "wfn.mm"
include "cc.mm"
include "cxp.mm"
include "c1.mm"
include "cneg.mm"
include "eqid.mm"
include "nvsf.mm"
include "neg1cn.mm"
include "curry1f.mm"
include "sylancl.mm"
include "ffn.mm"
include "syl.mm"
include "cgr.mm"
include "wf1o.mm"
include "nvgrp.mm"
include "bafval.mm"
include "grpoinvf.mm"
include "f1ofn.mm"
include "3syl.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "adantr.mm"
include "curry1val.mm"
include "nvinv.mm"
include "eqtrd.mm"
include "eqfnfvd.mm"

theorem nvinvfval
  let cS: class S
  let cU: class U
  let cG: class G
  let cN: class N
  let vx: setvar x
  assume nvinvfval.2: |- G = ( +v ` U )
  assume nvinvfval.4: |- S = ( .sOLD ` U )
  assume nvinvfval.3: |- N = ( S o. `' ( 2nd |` ( { -u 1 } X. _V ) ) )


  assert |- ( U e. NrmCVec -> N = ( inv ` G ) )

  proof
    cU
    cnv
    wcel
    #
    vx
    cU
    cba
    cfv
    #
    cN
    cG
    cgn
    cfv
    #
    @0
    @1
    @1
    cN
    wf
    #
    cN
    @1
    wfn
    @0
    cc
    @1
    cxp
    #
    @1
    cS
    wf
    #
    c1
    cneg
    #
    cc
    wcel
    #
    @3
    cS
    cU
    @1
    @1
    eqid
    #
    nvinvfval.4
    nvsf
    #
    neg1cn
    cc
    @1
    @6
    @1
    cS
    cN
    nvinvfval.3
    curry1f
    sylancl
    @1
    @1
    cN
    ffn
    syl
    @0
    cG
    cgr
    wcel
    @1
    @1
    @2
    wf1o
    @2
    @1
    wfn
    cU
    cG
    nvinvfval.2
    nvgrp
    cG
    @2
    @1
    cU
    cG
    @1
    @8
    nvinvfval.2
    bafval
    @2
    eqid
    #
    grpoinvf
    @1
    @1
    @2
    f1ofn
    3syl
    @0
    vx
    cv
    #
    @1
    wcel
    #
    wa
    #
    @11
    cN
    cfv
    #
    @6
    @11
    cS
    co
    #
    @11
    @2
    cfv
    @13
    cS
    @4
    wfn
    #
    @7
    @14
    @15
    wceq
    @0
    @16
    @12
    @0
    @5
    @16
    @9
    @4
    @1
    cS
    ffn
    syl
    adantr
    neg1cn
    cc
    @1
    @6
    @11
    cS
    cN
    nvinvfval.3
    curry1val
    sylancl
    @11
    cS
    cU
    cG
    @2
    @1
    @8
    nvinvfval.2
    nvinvfval.4
    @10
    nvinv
    eqtrd
    eqfnfvd
end
