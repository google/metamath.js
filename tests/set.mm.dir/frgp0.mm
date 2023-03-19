include "wcel.mm"
include "c2o.mm"
include "cxp.mm"
include "cfrmd.mm"
include "cfv.mm"
include "cplusg.mm"
include "cv.mm"
include "c1o.mm"
include "cdif.mm"
include "cop.mm"
include "cmpt2.mm"
include "creverse.mm"
include "ccom.mm"
include "cword.mm"
include "cvv.mm"
include "c0.mm"
include "eqid.mm"
include "frgpval.mm"
include "cbs.mm"
include "wceq.mm"
include "con0.mm"
include "2on.mm"
include "xpexg.mm"
include "mpan2.mm"
include "frmdbas.mm"
include "syl.mm"
include "eqcomd.mm"
include "eqidd.mm"
include "cid.mm"
include "wer.mm"
include "efger.mm"
include "wb.mm"
include "wrdexg.mm"
include "fvi.mm"
include "3syl.mm"
include "ereq2.mm"
include "mpbii.mm"
include "fvexd.mm"
include "wbr.mm"
include "wa.mm"
include "co.mm"
include "wi.mm"
include "frgpcpbl.mm"
include "a1i.mm"
include "w3a.mm"
include "cmnd.mm"
include "frmdmnd.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "eleqtrd.mm"
include "simp3.mm"
include "mndcl.mm"
include "syl3anc.mm"
include "eleqtrrd.mm"
include "adantr.mm"
include "3adant3r3.mm"
include "simpr3.mm"
include "erref.mm"
include "mndass.mm"
include "syl13anc.mm"
include "breqtrd.mm"
include "wrd0.mm"
include "cconcat.mm"
include "syl5eleq.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "frmdadd.mm"
include "syl2anc.mm"
include "ccatlid.mm"
include "adantl.mm"
include "eqtrd.mm"
include "simpr.mm"
include "eqbrtrd.mm"
include "wf.mm"
include "revcl.mm"
include "efgmf.mm"
include "wrdco.mm"
include "biimpar.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "cs2.mm"
include "cotp.mm"
include "csplice.mm"
include "cmpt.mm"
include "efginvrel1.mm"
include "qusgrp2.mm"

theorem frgp0
  let c.sm: class .~
  let cG: class G
  let cI: class I
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vn: setvar n
  let vv: setvar v
  let vw: setvar w
  assume frgp0.m: |- G = ( freeGrp ` I )
  assume frgp0.r: |- .~ = ( ~FG ` I )


  assert |- ( I e. V -> ( G e. Grp /\ [ (/) ] .~ = ( 0g ` G ) ) )

  proof
    cI
    cV
    wcel
    #
    vx
    vy
    vz
    cI
    c2o
    cxp
    #
    cfrmd
    cfv
    #
    cplusg
    cfv
    #
    c.sm
    @2
    cG
    vy
    vz
    cI
    c2o
    vy
    cv
    #
    c1o
    vz
    cv
    #
    cdif
    cop
    cmpt2
    #
    vx
    cv
    #
    creverse
    cfv
    #
    ccom
    #
    @1
    cword
    #
    cvv
    c0
    vd
    vb
    va
    vc
    c.sm
    cG
    cI
    @2
    cV
    frgp0.m
    @2
    eqid
    #
    frgp0.r
    frgpval
    @0
    @2
    cbs
    cfv
    #
    @10
    @0
    @1
    cvv
    wcel
    #
    @12
    @10
    wceq
    @0
    c2o
    con0
    wcel
    @13
    2on
    cI
    c2o
    cV
    con0
    xpexg
    mpan2
    #
    @12
    @1
    @2
    cvv
    @11
    @12
    eqid
    #
    frmdbas
    syl
    eqcomd
    #
    @0
    @3
    eqidd
    @0
    @10
    cid
    cfv
    #
    c.sm
    wer
    #
    @10
    c.sm
    wer
    #
    c.sm
    cI
    @17
    @17
    eqid
    #
    frgp0.r
    efger
    @0
    @17
    @10
    wceq
    #
    @18
    @19
    wb
    @0
    @13
    @10
    cvv
    wcel
    @21
    @14
    @1
    cvv
    wrdexg
    @10
    cvv
    fvi
    3syl
    #
    @17
    @10
    c.sm
    ereq2
    syl
    mpbii
    #
    @0
    @1
    cfrmd
    fvexd
    va
    cv
    #
    vb
    cv
    #
    c.sm
    wbr
    vc
    cv
    #
    vd
    cv
    #
    c.sm
    wbr
    wa
    @24
    @26
    @3
    co
    @25
    @27
    @3
    co
    c.sm
    wbr
    wi
    @0
    @24
    @26
    @25
    @27
    @3
    c.sm
    cG
    cI
    @2
    frgp0.m
    @11
    frgp0.r
    @3
    eqid
    #
    frgpcpbl
    a1i
    @0
    @7
    @10
    wcel
    #
    @4
    @10
    wcel
    #
    w3a
    #
    @7
    @4
    @3
    co
    #
    @12
    @10
    @31
    @2
    cmnd
    wcel
    #
    @7
    @12
    wcel
    #
    @4
    @12
    wcel
    #
    @32
    @12
    wcel
    #
    @0
    @29
    @33
    @30
    @0
    @13
    @33
    @14
    @1
    @2
    cvv
    @11
    frmdmnd
    syl
    #
    3ad2ant1
    @31
    @7
    @10
    @12
    @0
    @29
    @30
    simp2
    @0
    @29
    @10
    @12
    wceq
    #
    @30
    @16
    3ad2ant1
    #
    eleqtrd
    #
    @31
    @4
    @10
    @12
    @0
    @29
    @30
    simp3
    @39
    eleqtrd
    #
    @12
    @3
    @2
    @7
    @4
    @15
    @28
    mndcl
    syl3anc
    #
    @39
    eleqtrrd
    @0
    @29
    @30
    @5
    @10
    wcel
    #
    w3a
    #
    wa
    #
    @32
    @5
    @3
    co
    #
    @46
    @7
    @4
    @5
    @3
    co
    @3
    co
    #
    c.sm
    @45
    @46
    c.sm
    @10
    @0
    @19
    @44
    @23
    adantr
    @45
    @46
    @12
    @10
    @45
    @33
    @36
    @5
    @12
    wcel
    #
    @46
    @12
    wcel
    @0
    @33
    @44
    @37
    adantr
    #
    @0
    @29
    @30
    @36
    @43
    @42
    3adant3r3
    @45
    @5
    @10
    @12
    @0
    @29
    @30
    @43
    simpr3
    @0
    @38
    @44
    @16
    adantr
    #
    eleqtrd
    #
    @12
    @3
    @2
    @32
    @5
    @15
    @28
    mndcl
    syl3anc
    @50
    eleqtrrd
    erref
    @45
    @33
    @34
    @35
    @48
    @46
    @47
    wceq
    @49
    @0
    @29
    @30
    @34
    @43
    @40
    3adant3r3
    @0
    @29
    @30
    @35
    @43
    @41
    3adant3r3
    @51
    @12
    @3
    @2
    @7
    @4
    @5
    @15
    @28
    mndass
    syl13anc
    breqtrd
    c0
    @10
    wcel
    @0
    @1
    wrd0
    #
    a1i
    @0
    @29
    wa
    #
    c0
    @7
    @3
    co
    #
    @7
    @7
    c.sm
    @53
    @54
    c0
    @7
    cconcat
    co
    #
    @7
    @53
    c0
    @12
    wcel
    #
    @34
    @54
    @55
    wceq
    @0
    @56
    @29
    @0
    c0
    @10
    @12
    @52
    @16
    syl5eleq
    adantr
    @0
    @29
    @34
    @0
    @10
    @12
    @7
    @16
    eleq2d
    biimpa
    #
    @12
    @3
    @1
    @2
    c0
    @7
    @11
    @15
    @28
    frmdadd
    syl2anc
    @29
    @55
    @7
    wceq
    @0
    @1
    @7
    ccatlid
    adantl
    eqtrd
    @53
    @7
    c.sm
    @10
    @0
    @19
    @29
    @23
    adantr
    @0
    @29
    simpr
    erref
    eqbrtrd
    @53
    @8
    @10
    wcel
    #
    @1
    @1
    @6
    wf
    #
    @9
    @10
    wcel
    @29
    @58
    @0
    @1
    @7
    revcl
    adantl
    @59
    @53
    vy
    vz
    cI
    @6
    @6
    eqid
    #
    efgmf
    a1i
    @1
    @1
    @6
    @8
    wrdco
    syl2anc
    #
    @53
    @9
    @7
    @3
    co
    #
    @9
    @7
    cconcat
    co
    #
    c0
    c.sm
    @53
    @9
    @12
    wcel
    @34
    @62
    @63
    wceq
    @53
    @9
    @10
    @12
    @61
    @0
    @38
    @29
    @16
    adantr
    eleqtrd
    @57
    @12
    @3
    @1
    @2
    @9
    @7
    @11
    @15
    @28
    frmdadd
    syl2anc
    @53
    @7
    @17
    wcel
    #
    @63
    c0
    c.sm
    wbr
    @0
    @64
    @29
    @0
    @17
    @10
    @7
    @22
    eleq2d
    biimpar
    vy
    vz
    vw
    vv
    @7
    c.sm
    vv
    @17
    vn
    vw
    cc0
    vv
    cv
    #
    chash
    cfv
    cfz
    co
    @1
    @65
    vn
    cv
    #
    @66
    vw
    cv
    #
    @67
    @6
    cfv
    cs2
    cotp
    csplice
    co
    cmpt2
    cmpt
    #
    vn
    cI
    @6
    @17
    @20
    frgp0.r
    @60
    @68
    eqid
    efginvrel1
    syl
    eqbrtrd
    qusgrp2
end
