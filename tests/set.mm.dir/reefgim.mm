include "ce.mm"
include "cr.mm"
include "cres.mm"
include "crefld.mm"
include "cgim.mm"
include "co.mm"
include "wcel.mm"
include "cghm.mm"
include "crp.mm"
include "wf1o.mm"
include "wtru.mm"
include "caddc.mm"
include "cmul.mm"
include "rebase.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "cfv.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cress.mm"
include "csubg.mm"
include "cbs.mm"
include "wceq.mm"
include "eqid.mm"
include "rpmsubg.mm"
include "cvv.mm"
include "wss.mm"
include "cnex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "cv.mm"
include "wne.mm"
include "rpcn.mm"
include "rpne0.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "ssriv.mm"
include "ressabs.mm"
include "mp2an.mm"
include "eqtr4i.mm"
include "subgbas.mm"
include "replusg.mm"
include "cplusg.mm"
include "cnfldmul.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "crg.mm"
include "cgrp.mm"
include "csubrg.mm"
include "cdr.mm"
include "resubdrg.mm"
include "simpli.mm"
include "df-refld.mm"
include "subrgring.mm"
include "ringgrp.mm"
include "mp1i.mm"
include "subggrp.mm"
include "wf.mm"
include "reeff1o.mm"
include "f1of.mm"
include "wa.mm"
include "recn.mm"
include "efadd.mm"
include "syl2an.mm"
include "readdcl.mm"
include "fvres.mm"
include "syl.mm"
include "oveqan12d.mm"
include "3eqtr4d.mm"
include "adantl.mm"
include "isghmd.mm"
include "trud.mm"
include "isgim.mm"
include "mpbir2an.mm"

theorem reefgim
  let cP: class P
  let vx: setvar x
  let vy: setvar y
  assume reefgim.1: |- P = ( ( mulGrp ` CCfld ) |`s RR+ )


  assert |- ( exp |` RR ) e. ( RRfld GrpIso P )

  proof
    ce
    cr
    cres
    #
    crefld
    cP
    cgim
    co
    wcel
    @0
    crefld
    cP
    cghm
    co
    wcel
    #
    cr
    crp
    @0
    wf1o
    #
    @1
    wtru
    vx
    vy
    caddc
    cmul
    crefld
    cP
    @0
    cr
    crp
    rebase
    crp
    ccnfld
    cmgp
    cfv
    #
    cc
    cc0
    csn
    #
    cdif
    #
    cress
    co
    #
    csubg
    cfv
    #
    wcel
    #
    crp
    cP
    cbs
    cfv
    wceq
    @6
    @6
    eqid
    rpmsubg
    #
    crp
    @6
    cP
    cP
    @3
    crp
    cress
    co
    #
    @6
    crp
    cress
    co
    #
    reefgim.1
    @5
    cvv
    wcel
    #
    crp
    @5
    wss
    @11
    @10
    wceq
    cc
    cvv
    wcel
    @12
    cnex
    cc
    @4
    cvv
    difexg
    ax-mp
    vx
    crp
    @5
    vx
    cv
    #
    crp
    wcel
    @13
    cc
    wcel
    #
    @13
    cc0
    wne
    @13
    @5
    wcel
    @13
    rpcn
    @13
    rpne0
    @13
    cc
    cc0
    eldifsn
    sylanbrc
    ssriv
    @5
    crp
    @3
    cvv
    ressabs
    mp2an
    eqtr4i
    #
    subgbas
    ax-mp
    #
    replusg
    @8
    cmul
    cP
    cplusg
    cfv
    wceq
    @9
    crp
    cmul
    @3
    cP
    @7
    reefgim.1
    ccnfld
    cmul
    @3
    @3
    eqid
    cnfldmul
    mgpplusg
    ressplusg
    ax-mp
    crefld
    crg
    wcel
    #
    crefld
    cgrp
    wcel
    wtru
    cr
    ccnfld
    csubrg
    cfv
    wcel
    #
    @17
    @18
    crefld
    cdr
    wcel
    resubdrg
    simpli
    cr
    ccnfld
    crefld
    df-refld
    subrgring
    ax-mp
    crefld
    ringgrp
    mp1i
    @8
    cP
    cgrp
    wcel
    wtru
    @9
    crp
    @6
    cP
    @15
    subggrp
    mp1i
    @2
    cr
    crp
    @0
    wf
    wtru
    reeff1o
    cr
    crp
    @0
    f1of
    mp1i
    @13
    cr
    wcel
    #
    vy
    cv
    #
    cr
    wcel
    #
    wa
    #
    @13
    @20
    caddc
    co
    #
    @0
    cfv
    #
    @13
    @0
    cfv
    #
    @20
    @0
    cfv
    #
    cmul
    co
    #
    wceq
    wtru
    @22
    @23
    ce
    cfv
    #
    @13
    ce
    cfv
    #
    @20
    ce
    cfv
    #
    cmul
    co
    #
    @24
    @27
    @19
    @14
    @20
    cc
    wcel
    @28
    @31
    wceq
    @21
    @13
    recn
    @20
    recn
    @13
    @20
    efadd
    syl2an
    @22
    @23
    cr
    wcel
    @24
    @28
    wceq
    @13
    @20
    readdcl
    @23
    cr
    ce
    fvres
    syl
    @19
    @21
    @25
    @29
    @26
    @30
    cmul
    @13
    cr
    ce
    fvres
    @20
    cr
    ce
    fvres
    oveqan12d
    3eqtr4d
    adantl
    isghmd
    trud
    reeff1o
    cr
    crp
    crefld
    cP
    @0
    rebase
    @16
    isgim
    mpbir2an
end
