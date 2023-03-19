include "cngp.mm"
include "wcel.mm"
include "cr.mm"
include "wf.mm"
include "cxp.mm"
include "nmf.mm"
include "cme.mm"
include "cfv.mm"
include "cnm.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "ctng.mm"
include "co.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "nrmtngnrm.mm"
include "cgrp.mm"
include "tngngp2.mm"
include "simpr.mm"
include "syl6bi.mm"
include "com12.mm"
include "adantr.mm"
include "syl.mm"
include "metf.mm"
include "syl6.mm"
include "mpd.mm"

theorem tngngpim
  let cD: class D
  let cT: class T
  let cG: class G
  let cN: class N
  let cX: class X
  assume tngngpim.t: |- T = ( G toNrmGrp N )
  assume tngngpim.n: |- N = ( norm ` G )
  assume tngngpim.x: |- X = ( Base ` G )
  assume tngngpim.d: |- D = ( dist ` T )


  assert |- ( G e. NrmGrp -> D : ( X X. X ) --> RR )

  proof
    cG
    cngp
    wcel
    #
    cX
    cr
    cN
    wf
    #
    cX
    cX
    cxp
    cr
    cD
    wf
    #
    cG
    cN
    cX
    tngngpim.x
    tngngpim.n
    nmf
    @0
    @1
    cD
    cX
    cme
    cfv
    wcel
    #
    @2
    @0
    cT
    cngp
    wcel
    #
    cT
    cnm
    cfv
    cG
    cnm
    cfv
    #
    wceq
    #
    wa
    @1
    @3
    wi
    #
    cT
    cG
    cT
    cG
    cN
    ctng
    co
    cG
    @5
    ctng
    co
    tngngpim.t
    cN
    @5
    cG
    ctng
    tngngpim.n
    oveq2i
    eqtri
    nrmtngnrm
    @4
    @7
    @6
    @1
    @4
    @3
    @1
    @4
    cG
    cgrp
    wcel
    #
    @3
    wa
    @3
    cD
    cT
    cG
    cN
    cX
    tngngpim.t
    tngngpim.x
    tngngpim.d
    tngngp2
    @8
    @3
    simpr
    syl6bi
    com12
    adantr
    syl
    cD
    cX
    metf
    syl6
    mpd
end
