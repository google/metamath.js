include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cv.mm"
include "csgrp.mm"
include "wnel.mm"
include "cmgm.mm"
include "wrex.mm"
include "prhash2ex.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "wa.mm"
include "cif.mm"
include "cmpt2.mm"
include "cvv.mm"
include "wcel.mm"
include "c0ex.mm"
include "1ex.mm"
include "pm3.2i.mm"
include "eqid.mm"
include "prex.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "ifbid.mm"
include "anbi2d.mm"
include "cbvmpt2v.mm"
include "opeq2i.mm"
include "preq2i.mm"
include "grpbase.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "mpt2ex.mm"
include "grpplusg.mm"
include "mgm2nsgrplem1.mm"
include "mp1i.mm"
include "wb.mm"
include "neleq1.mm"
include "adantl.mm"
include "mgm2nsgrplem4.mm"
include "rspcedvd.mm"

theorem mgmnsgrpex
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let vv: setvar v


  assert |- E. m e. Mgm m e/ SGrp

  proof
    cc0
    c1
    cpr
    #
    chash
    cfv
    c2
    wceq
    #
    vm
    cv
    #
    csgrp
    wnel
    #
    vm
    cmgm
    wrex
    prhash2ex
    @1
    @3
    cnx
    cbs
    cfv
    @0
    cop
    #
    cnx
    cplusg
    cfv
    #
    vx
    vy
    @0
    @0
    vx
    cv
    #
    cc0
    wceq
    #
    vy
    cv
    #
    cc0
    wceq
    #
    wa
    #
    c1
    cc0
    cif
    #
    cmpt2
    #
    cop
    #
    cpr
    #
    csgrp
    wnel
    #
    vm
    @14
    cmgm
    cc0
    cvv
    wcel
    #
    c1
    cvv
    wcel
    #
    wa
    @14
    cmgm
    wcel
    @1
    @16
    @17
    c0ex
    1ex
    pm3.2i
    vu
    vv
    cc0
    c1
    @0
    @14
    cvv
    cvv
    @0
    eqid
    #
    @0
    @14
    cbs
    cfv
    #
    @0
    cvv
    wcel
    @0
    @19
    wceq
    cc0
    c1
    prex
    #
    @0
    vu
    vv
    @0
    @0
    vu
    cv
    #
    cc0
    wceq
    #
    vv
    cv
    #
    cc0
    wceq
    #
    wa
    #
    c1
    cc0
    cif
    #
    cmpt2
    #
    @14
    cvv
    @13
    @5
    @27
    cop
    @4
    @12
    @27
    @5
    vx
    vy
    vu
    vv
    @0
    @0
    @11
    @26
    @22
    @9
    wa
    #
    c1
    cc0
    cif
    @6
    @21
    wceq
    #
    @10
    @28
    c1
    cc0
    @29
    @7
    @22
    @9
    @6
    @21
    cc0
    eqeq1
    anbi1d
    ifbid
    @8
    @23
    wceq
    #
    @28
    @25
    c1
    cc0
    @30
    @9
    @24
    @22
    @8
    @23
    cc0
    eqeq1
    anbi2d
    ifbid
    cbvmpt2v
    opeq2i
    preq2i
    #
    grpbase
    ax-mp
    eqcomi
    #
    @27
    @14
    cplusg
    cfv
    #
    @27
    cvv
    wcel
    @27
    @33
    wceq
    vu
    vv
    @0
    @0
    @26
    @20
    @20
    mpt2ex
    @0
    @27
    @14
    cvv
    @31
    grpplusg
    ax-mp
    eqcomi
    #
    mgm2nsgrplem1
    mp1i
    @2
    @14
    wceq
    @3
    @15
    wb
    @1
    @2
    @14
    csgrp
    neleq1
    adantl
    vu
    vv
    cc0
    c1
    @0
    @14
    @18
    @32
    @34
    mgm2nsgrplem4
    rspcedvd
    ax-mp
end
