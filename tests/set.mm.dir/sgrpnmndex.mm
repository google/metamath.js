include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cv.mm"
include "cmnd.mm"
include "wnel.mm"
include "csgrp.mm"
include "wrex.mm"
include "prhash2ex.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "cif.mm"
include "cmpt2.mm"
include "eqid.mm"
include "cvv.mm"
include "wcel.mm"
include "prex.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "eqidd.mm"
include "cbvmpt2v.mm"
include "opeq2i.mm"
include "preq2i.mm"
include "grpbase.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "mpt2ex.mm"
include "grpplusg.mm"
include "sgrp2nmndlem4.mm"
include "wb.mm"
include "neleq1.mm"
include "adantl.mm"
include "sgrp2nmndlem5.mm"
include "rspcedvd.mm"

theorem sgrpnmndex
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let vv: setvar v


  assert |- E. m e. SGrp m e/ Mnd

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
    cmnd
    wnel
    #
    vm
    csgrp
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
    cc0
    c1
    cif
    #
    cmpt2
    #
    cop
    #
    cpr
    #
    cmnd
    wnel
    #
    vm
    @11
    csgrp
    vu
    vv
    cc0
    c1
    @0
    @11
    @0
    eqid
    #
    @0
    @11
    cbs
    cfv
    #
    @0
    cvv
    wcel
    @0
    @14
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
    cc0
    c1
    cif
    #
    cmpt2
    #
    @11
    cvv
    @10
    @5
    @19
    cop
    @4
    @9
    @19
    @5
    vx
    vy
    vu
    vv
    @0
    @0
    @8
    @18
    @18
    @6
    @16
    wceq
    @7
    @17
    cc0
    c1
    @6
    @16
    cc0
    eqeq1
    ifbid
    vy
    cv
    vv
    cv
    wceq
    @18
    eqidd
    cbvmpt2v
    opeq2i
    preq2i
    #
    grpbase
    ax-mp
    eqcomi
    #
    @19
    @11
    cplusg
    cfv
    #
    @19
    cvv
    wcel
    @19
    @22
    wceq
    vu
    vv
    @0
    @0
    @18
    @15
    @15
    mpt2ex
    @0
    @19
    @11
    cvv
    @20
    grpplusg
    ax-mp
    eqcomi
    #
    sgrp2nmndlem4
    @2
    @11
    wceq
    @3
    @12
    wb
    @1
    @2
    @11
    cmnd
    neleq1
    adantl
    vu
    vv
    cc0
    c1
    @0
    @11
    @13
    @21
    @23
    sgrp2nmndlem5
    rspcedvd
    ax-mp
end
