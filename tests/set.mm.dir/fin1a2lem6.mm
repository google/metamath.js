include "crn.mm"
include "cima.mm"
include "cres.mm"
include "wf1o.mm"
include "com.mm"
include "cdif.mm"
include "con0.mm"
include "wf1.mm"
include "wss.mm"
include "fin1a2lem2.mm"
include "wf.mm"
include "fin1a2lem4.mm"
include "f1f.mm"
include "frn.mm"
include "omsson.mm"
include "syl6ss.mm"
include "mp2b.mm"
include "f1ores.mm"
include "mp2an.mm"
include "wceq.mm"
include "wb.mm"
include "cv.mm"
include "cfv.mm"
include "wrex.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "csuc.mm"
include "sseli.mm"
include "fin1a2lem1.mm"
include "syl.mm"
include "eqeq1d.mm"
include "rexbiia.mm"
include "peano2.mm"
include "fin1a2lem5.mm"
include "biimpd.mm"
include "mpcom.mm"
include "jca.mm"
include "eleq1.mm"
include "notbid.mm"
include "anbi12d.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "c0.mm"
include "wne.mm"
include "c2o.mm"
include "comu.mm"
include "co.mm"
include "peano1.mm"
include "fin1a2lem3.mm"
include "ax-mp.mm"
include "om0x.mm"
include "eqtri.mm"
include "wfun.mm"
include "cdm.mm"
include "f1fun.mm"
include "f1dm.mm"
include "eleqtrri.mm"
include "fvelrn.mm"
include "eqeltrri.mm"
include "mpbiri.mm"
include "necon3bi.mm"
include "nnsuc.mm"
include "sylan2.mm"
include "anbi1d.mm"
include "simplr.mm"
include "adantl.mm"
include "mpbird.mm"
include "syl6bi.mm"
include "com12.mm"
include "impr.mm"
include "simprr.mm"
include "eqcomd.mm"
include "ex.mm"
include "reximdv2.mm"
include "mpd.mm"
include "impbii.mm"
include "bitri.mm"
include "wfn.mm"
include "f1fn.mm"
include "fvelimab.mm"
include "eldif.mm"
include "3bitr4i.mm"
include "eqriv.mm"
include "f1oeq3.mm"
include "mpbi.mm"

theorem fin1a2lem6
  let vx: setvar x
  let cS: class S
  let cE: class E
  let va: setvar a
  let vf: setvar f
  let vy: setvar y
  let cA: class A
  let vb: setvar b
  assume fin1a2lem.b: |- E = ( x e. _om |-> ( 2o .o x ) )
  assume fin1a2lem.aa: |- S = ( x e. On |-> suc x )


  assert |- ( S |` ran E ) : ran E -1-1-onto-> ( _om \ ran E )

  proof
    cE
    crn
    #
    cS
    @0
    cima
    #
    cS
    @0
    cres
    #
    wf1o
    #
    @0
    com
    @0
    cdif
    #
    @2
    wf1o
    #
    con0
    con0
    cS
    wf1
    #
    @0
    con0
    wss
    #
    @3
    vx
    cS
    fin1a2lem.aa
    fin1a2lem2
    #
    com
    com
    cE
    wf1
    #
    com
    com
    cE
    wf
    #
    @7
    vx
    cE
    fin1a2lem.b
    fin1a2lem4
    #
    com
    com
    cE
    f1f
    #
    @10
    @0
    com
    con0
    com
    com
    cE
    frn
    #
    omsson
    syl6ss
    mp2b
    #
    con0
    con0
    @0
    cS
    f1ores
    mp2an
    @1
    @4
    wceq
    @3
    @5
    wb
    va
    @1
    @4
    vb
    cv
    #
    cS
    cfv
    #
    va
    cv
    #
    wceq
    #
    vb
    @0
    wrex
    #
    @17
    com
    wcel
    #
    @17
    @0
    wcel
    #
    wn
    #
    wa
    #
    @17
    @1
    wcel
    #
    @17
    @4
    wcel
    @19
    @15
    csuc
    #
    @17
    wceq
    #
    vb
    @0
    wrex
    #
    @23
    @18
    @26
    vb
    @0
    @15
    @0
    wcel
    #
    @16
    @25
    @17
    @28
    @15
    con0
    wcel
    @16
    @25
    wceq
    @0
    con0
    @15
    @14
    sseli
    vx
    @15
    cS
    fin1a2lem.aa
    fin1a2lem1
    syl
    eqeq1d
    rexbiia
    @27
    @23
    @26
    @23
    vb
    @0
    @28
    @25
    com
    wcel
    #
    @25
    @0
    wcel
    #
    wn
    #
    wa
    #
    @26
    @23
    @28
    @29
    @31
    @28
    @15
    com
    wcel
    #
    @29
    @0
    com
    @15
    @9
    @10
    @0
    com
    wss
    @11
    @12
    @13
    mp2b
    sseli
    #
    @15
    peano2
    syl
    @33
    @28
    @31
    @34
    @33
    @28
    @31
    vx
    @15
    cE
    fin1a2lem.b
    fin1a2lem5
    #
    biimpd
    mpcom
    jca
    @26
    @29
    @20
    @31
    @22
    @25
    @17
    com
    eleq1
    @26
    @30
    @21
    @25
    @17
    @0
    eleq1
    notbid
    anbi12d
    syl5ibcom
    rexlimiv
    @23
    @17
    @25
    wceq
    #
    vb
    com
    wrex
    #
    @27
    @22
    @20
    @17
    c0
    wne
    @37
    @21
    @17
    c0
    @17
    c0
    wceq
    @21
    c0
    @0
    wcel
    c0
    cE
    cfv
    #
    c0
    @0
    @38
    c2o
    c0
    comu
    co
    #
    c0
    c0
    com
    wcel
    @38
    @39
    wceq
    peano1
    vx
    c0
    cE
    fin1a2lem.b
    fin1a2lem3
    ax-mp
    c2o
    om0x
    eqtri
    cE
    wfun
    #
    c0
    cE
    cdm
    #
    wcel
    @38
    @0
    wcel
    @9
    @40
    @11
    com
    com
    cE
    f1fun
    ax-mp
    c0
    com
    @41
    peano1
    @9
    @41
    com
    wceq
    @11
    com
    com
    cE
    f1dm
    ax-mp
    eleqtrri
    c0
    cE
    fvelrn
    mp2an
    eqeltrri
    @17
    c0
    @0
    eleq1
    mpbiri
    necon3bi
    vb
    @17
    nnsuc
    sylan2
    @23
    @36
    @26
    vb
    com
    @0
    @23
    @33
    @36
    wa
    #
    @28
    @26
    wa
    @23
    @42
    wa
    #
    @28
    @26
    @23
    @33
    @36
    @28
    @36
    @23
    @33
    wa
    #
    @28
    @36
    @44
    @32
    @33
    wa
    #
    @28
    @36
    @23
    @32
    @33
    @36
    @20
    @29
    @22
    @31
    @17
    @25
    com
    eleq1
    @36
    @21
    @30
    @17
    @25
    @0
    eleq1
    notbid
    anbi12d
    anbi1d
    @45
    @28
    @31
    @29
    @31
    @33
    simplr
    @33
    @28
    @31
    wb
    @32
    @35
    adantl
    mpbird
    syl6bi
    com12
    impr
    @43
    @17
    @25
    @23
    @33
    @36
    simprr
    eqcomd
    jca
    ex
    reximdv2
    mpd
    impbii
    bitri
    cS
    con0
    wfn
    #
    @7
    @24
    @19
    wb
    @6
    @46
    @8
    con0
    con0
    cS
    f1fn
    ax-mp
    @14
    vb
    con0
    @0
    @17
    cS
    fvelimab
    mp2an
    @17
    com
    @0
    eldif
    3bitr4i
    eqriv
    @1
    @4
    @0
    @2
    f1oeq3
    ax-mp
    mpbi
end
