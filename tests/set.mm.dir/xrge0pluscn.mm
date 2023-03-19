include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cpnf.mm"
include "cmul.mm"
include "cxp.mm"
include "cres.mm"
include "cii.mm"
include "xrge0iifhmeo.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "cc.mm"
include "wss.mm"
include "unitsscn.mm"
include "xpss12.mm"
include "mp2an.mm"
include "wb.mm"
include "ax-mulf.mm"
include "ffn.mm"
include "fnssresb.mm"
include "mp2b.mm"
include "mpbir.mm"
include "wa.mm"
include "ovres.mm"
include "iimulcl.mm"
include "eqeltrd.mm"
include "rgen2a.mm"
include "ffnov.mm"
include "mpbir2an.mm"
include "cxad.mm"
include "cxr.mm"
include "iccssxr.mm"
include "xaddf.mm"
include "fneq1i.mm"
include "oveqi.mm"
include "ge0xaddcl.mm"
include "syl5eqel.mm"
include "iitopon.mm"
include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "crest.mm"
include "ctopon.mm"
include "letopon.mm"
include "resttopon.mm"
include "eqeltri.mm"
include "wceq.mm"
include "wf1o.mm"
include "ccnv.mm"
include "cneg.mm"
include "ce.mm"
include "cif.mm"
include "cmpt.mm"
include "xrge0iifcnv.mm"
include "simpli.mm"
include "f1of.mm"
include "ax-mp.mm"
include "ffvelrni.mm"
include "syl2an.mm"
include "syl5eq.mm"
include "xrge0iifhom.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "3eqtr2rd.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "cress.mm"
include "ctmd.mm"
include "ctx.mm"
include "ccn.mm"
include "eqid.mm"
include "iistmd.mm"
include "cvv.mm"
include "cnfldex.mm"
include "ovex.mm"
include "mgpress.mm"
include "dfii4.mm"
include "mgptopn.mm"
include "cplusf.mm"
include "cnfldbas.mm"
include "mgpbas.mm"
include "cnfldmul.mm"
include "mgpplusg.mm"
include "ressplusf.mm"
include "eqcomi.mm"
include "tmdcn.mm"
include "mndpluscn.mm"

theorem xrge0pluscn
  let vx: setvar x
  let c.pl: class .+
  let cF: class F
  let cJ: class J
  let vy: setvar y
  let cX: class X
  let vw: setvar w
  let vz: setvar z
  let vu: setvar u
  let cY: class Y
  let vv: setvar v
  let va: setvar a
  let vb: setvar b
  assume xrge0iifhmeo.1: |- F = ( x e. ( 0 [,] 1 ) |-> if ( x = 0 , +oo , -u ( log ` x ) ) )
  assume xrge0iifhmeo.k: |- J = ( ( ordTop ` <_ ) |`t ( 0 [,] +oo ) )
  assume xrge0pluscn.1: |- .+ = ( +e |` ( ( 0 [,] +oo ) X. ( 0 [,] +oo ) ) )

  disjoint F x
  disjoint x y
  disjoint X x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint u x
  disjoint Y x
  disjoint v x
  disjoint a b
  disjoint .+ a
  disjoint .+ b
  disjoint u v
  disjoint .+ u
  disjoint .+ v
  disjoint F u
  disjoint F v
  assert |- .+ e. ( ( J tX J ) Cn J )

  proof
    vu
    vv
    cc0
    c1
    cicc
    co
    #
    cc0
    cpnf
    cicc
    co
    #
    cmul
    @0
    @0
    cxp
    #
    cres
    #
    cF
    c.pl
    cii
    cJ
    vx
    cF
    cJ
    xrge0iifhmeo.1
    xrge0iifhmeo.k
    xrge0iifhmeo
    @2
    @0
    @3
    wf
    @3
    @2
    wfn
    #
    vu
    cv
    #
    vv
    cv
    #
    @3
    co
    #
    @0
    wcel
    #
    vv
    @0
    wral
    vu
    @0
    wral
    @4
    @2
    cc
    cc
    cxp
    #
    wss
    #
    @0
    cc
    wss
    #
    @11
    @10
    unitsscn
    unitsscn
    @0
    cc
    @0
    cc
    xpss12
    mp2an
    @9
    cc
    cmul
    wf
    #
    cmul
    @9
    wfn
    #
    @4
    @10
    wb
    ax-mulf
    @9
    cc
    cmul
    ffn
    #
    @9
    @2
    cmul
    fnssresb
    mp2b
    mpbir
    @8
    vu
    vv
    @0
    @5
    @0
    wcel
    #
    @6
    @0
    wcel
    #
    wa
    #
    @7
    @5
    @6
    cmul
    co
    #
    @0
    @5
    @6
    @0
    @0
    cmul
    ovres
    #
    @5
    @6
    iimulcl
    eqeltrd
    rgen2a
    vu
    vv
    @0
    @0
    @0
    @3
    ffnov
    mpbir2an
    @1
    @1
    cxp
    #
    @1
    c.pl
    wf
    c.pl
    @20
    wfn
    #
    va
    cv
    #
    vb
    cv
    #
    c.pl
    co
    #
    @1
    wcel
    #
    vb
    @1
    wral
    va
    @1
    wral
    @21
    cxad
    @20
    cres
    #
    @20
    wfn
    #
    @27
    @20
    cxr
    cxr
    cxp
    #
    wss
    #
    @1
    cxr
    wss
    #
    @30
    @29
    cc0
    cpnf
    iccssxr
    #
    @31
    @1
    cxr
    @1
    cxr
    xpss12
    mp2an
    @28
    cxr
    cxad
    wf
    cxad
    @28
    wfn
    @27
    @29
    wb
    xaddf
    @28
    cxr
    cxad
    ffn
    @28
    @20
    cxad
    fnssresb
    mp2b
    mpbir
    @20
    c.pl
    @26
    xrge0pluscn.1
    fneq1i
    mpbir
    @25
    va
    vb
    @1
    @22
    @1
    wcel
    @23
    @1
    wcel
    wa
    #
    @24
    @22
    @23
    @26
    co
    #
    @1
    c.pl
    @26
    @22
    @23
    xrge0pluscn.1
    oveqi
    @32
    @33
    @22
    @23
    cxad
    co
    @1
    @22
    @23
    @1
    @1
    cxad
    ovres
    @22
    @23
    ge0xaddcl
    eqeltrd
    syl5eqel
    rgen2a
    va
    vb
    @1
    @1
    @1
    c.pl
    ffnov
    mpbir2an
    iitopon
    cJ
    cle
    cordt
    cfv
    #
    @1
    crest
    co
    #
    @1
    ctopon
    cfv
    #
    xrge0iifhmeo.k
    @34
    cxr
    ctopon
    cfv
    wcel
    @30
    @35
    @36
    wcel
    letopon
    @31
    @1
    @34
    cxr
    resttopon
    mp2an
    eqeltri
    @17
    @5
    cF
    cfv
    #
    @6
    cF
    cfv
    #
    c.pl
    co
    #
    @37
    @38
    cxad
    co
    #
    @18
    cF
    cfv
    @7
    cF
    cfv
    @17
    @39
    @37
    @38
    @26
    co
    #
    @40
    c.pl
    @26
    @37
    @38
    xrge0pluscn.1
    oveqi
    @15
    @37
    @1
    wcel
    @38
    @1
    wcel
    @41
    @40
    wceq
    @16
    @0
    @1
    @5
    cF
    @0
    @1
    cF
    wf1o
    #
    @0
    @1
    cF
    wf
    @42
    cF
    ccnv
    vy
    @1
    vy
    cv
    #
    cpnf
    wceq
    cc0
    @43
    cneg
    ce
    cfv
    cif
    cmpt
    wceq
    vx
    vy
    cF
    xrge0iifhmeo.1
    xrge0iifcnv
    simpli
    @0
    @1
    cF
    f1of
    ax-mp
    #
    ffvelrni
    @0
    @1
    @6
    cF
    @44
    ffvelrni
    @37
    @38
    @1
    @1
    cxad
    ovres
    syl2an
    syl5eq
    vx
    cF
    cJ
    @5
    @6
    xrge0iifhmeo.1
    xrge0iifhmeo.k
    xrge0iifhom
    @17
    @18
    @7
    cF
    @17
    @7
    @18
    @19
    eqcomd
    fveq2d
    3eqtr2rd
    ccnfld
    cmgp
    cfv
    #
    @0
    cress
    co
    #
    ctmd
    wcel
    @3
    cii
    cii
    ctx
    co
    cii
    ccn
    co
    wcel
    @46
    @46
    eqid
    #
    iistmd
    @3
    @46
    cii
    ccnfld
    @0
    cress
    co
    #
    cii
    @46
    ccnfld
    cvv
    wcel
    @0
    cvv
    wcel
    @46
    @48
    cmgp
    cfv
    wceq
    cnfldex
    cc0
    c1
    cicc
    ovex
    @0
    ccnfld
    @48
    @45
    cvv
    cvv
    @48
    eqid
    #
    @45
    eqid
    #
    mgpress
    mp2an
    @48
    @49
    dfii4
    mgptopn
    @46
    cplusf
    cfv
    @3
    @0
    cc
    cmul
    @45
    @46
    cc
    ccnfld
    @45
    @50
    cnfldbas
    mgpbas
    @47
    ccnfld
    cmul
    @45
    @50
    cnfldmul
    mgpplusg
    @12
    @13
    ax-mulf
    @14
    ax-mp
    unitsscn
    ressplusf
    eqcomi
    tmdcn
    ax-mp
    mndpluscn
end
