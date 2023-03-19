include "cc.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cmpt2.mm"
include "ccnfld.mm"
include "csg.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cminusg.mm"
include "caddc.mm"
include "cneg.mm"
include "cnfldbas.mm"
include "cnfldadd.mm"
include "eqid.mm"
include "grpsubval.mm"
include "wceq.mm"
include "cnfldneg.mm"
include "adantl.mm"
include "oveq2d.mm"
include "negsub.mm"
include "3eqtrrd.mm"
include "mpt2eq3ia.mm"
include "cxp.mm"
include "wfn.mm"
include "wf.mm"
include "subf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fnov.mm"
include "mpbi.mm"
include "cgrp.mm"
include "crg.mm"
include "cnring.mm"
include "ringgrp.mm"
include "grpsubf.mm"
include "mp2b.mm"
include "3eqtr4i.mm"

theorem cnfldsub
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- - = ( -g ` CCfld )

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
    @1
    ccnfld
    csg
    cfv
    #
    co
    #
    cmpt2
    #
    cmin
    @4
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
    ccnfld
    cminusg
    cfv
    #
    cfv
    #
    caddc
    co
    @0
    @1
    cneg
    #
    caddc
    co
    @2
    cc
    caddc
    ccnfld
    @10
    @4
    @0
    @1
    cnfldbas
    cnfldadd
    @10
    eqid
    @4
    eqid
    #
    grpsubval
    @9
    @11
    @12
    @0
    caddc
    @8
    @11
    @12
    wceq
    @7
    @1
    cnfldneg
    adantl
    oveq2d
    @0
    @1
    negsub
    3eqtrrd
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
    @14
    cc
    cmin
    wf
    @15
    subf
    @14
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
    @4
    @14
    wfn
    #
    @4
    @6
    wceq
    ccnfld
    cgrp
    wcel
    #
    @14
    cc
    @4
    wf
    @16
    ccnfld
    crg
    wcel
    @17
    cnring
    ccnfld
    ringgrp
    ax-mp
    cc
    ccnfld
    @4
    cnfldbas
    @13
    grpsubf
    @14
    cc
    @4
    ffn
    mp2b
    vx
    vy
    cc
    cc
    @4
    fnov
    mpbi
    3eqtr4i
end
