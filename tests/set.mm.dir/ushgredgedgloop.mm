include "cushgr.mm"
include "wcel.mm"
include "wa.mm"
include "wf1o.mm"
include "cv.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "cdm.mm"
include "crab.mm"
include "cima.mm"
include "cres.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "cdif.mm"
include "wf1.mm"
include "wss.mm"
include "eqid.mm"
include "ushgrf.mm"
include "adantr.mm"
include "ssrab2.mm"
include "f1ores.mm"
include "sylancl.mm"
include "cmpt.mm"
include "a1i.mm"
include "eqidd.mm"
include "mpteq12dva.mm"
include "syl5eq.mm"
include "wf.mm"
include "f1f.mm"
include "syl.mm"
include "feqresmpt.mm"
include "eqtr4d.mm"
include "wrex.mm"
include "cab.mm"
include "wfun.mm"
include "ciedg.mm"
include "cuhgr.mm"
include "ushgruhgr.mm"
include "uhgrfun.mm"
include "funeqi.mm"
include "sylibr.mm"
include "dfimafn.mm"
include "wi.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "w3a.mm"
include "crn.mm"
include "simpl.mm"
include "fvelrn.mm"
include "eqcomi.mm"
include "rneqi.mm"
include "syl6eleqr.mm"
include "syl2an.mm"
include "3adant3.mm"
include "wb.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "3ad2ant3.mm"
include "mpbird.mm"
include "cedg.mm"
include "edgval.mm"
include "eleq2d.mm"
include "3ad2ant1.mm"
include "eqeq1.mm"
include "biimpcd.mm"
include "adantl.mm"
include "3imp.mm"
include "jca.mm"
include "3exp.mm"
include "syl5bi.mm"
include "rexlimdv.mm"
include "wfn.mm"
include "funfn.mm"
include "biimpi.mm"
include "fvelrnb.mm"
include "dmeqi.mm"
include "eleq2i.mm"
include "fveq1i.mm"
include "eqeq2i.mm"
include "adantld.mm"
include "imp.mm"
include "eqeq1i.mm"
include "ex.mm"
include "reximdv2.mm"
include "com23.mm"
include "sylbid.mm"
include "impd.mm"
include "impbid.mm"
include "vex.mm"
include "eqeq2.mm"
include "rexbidv.mm"
include "elab.mm"
include "elrab2.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "eqtr2d.mm"
include "f1oeq123d.mm"

theorem ushgredgedgloop
  let vx: setvar x
  let cA: class A
  let cB: class B
  let ve: setvar e
  let vi: setvar i
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cN: class N
  let cV: class V
  let vf: setvar f
  let vj: setvar j
  assume ushgredgedgloop.e: |- E = ( Edg ` G )
  assume ushgredgedgloop.i: |- I = ( iEdg ` G )
  assume ushgredgedgloop.v: |- V = ( Vtx ` G )
  assume ushgredgedgloop.a: |- A = { i e. dom I | ( I ` i ) = { N } }
  assume ushgredgedgloop.b: |- B = { e e. E | e = { N } }
  assume ushgredgedgloop.f: |- F = ( x e. A |-> ( I ` x ) )

  disjoint B e
  disjoint E e
  disjoint E i
  disjoint e i
  disjoint G e
  disjoint G i
  disjoint G x
  disjoint I e
  disjoint I i
  disjoint I x
  disjoint e x
  disjoint i x
  disjoint N e
  disjoint N i
  disjoint N x
  disjoint V e
  disjoint V i
  disjoint V x
  disjoint B f
  disjoint e f
  disjoint E j
  disjoint e j
  disjoint i j
  disjoint G f
  disjoint G j
  disjoint f i
  disjoint f j
  disjoint I f
  disjoint I j
  disjoint N f
  disjoint N j
  disjoint V f
  disjoint V j
  assert |- ( ( G e. USHGraph /\ N e. V ) -> F : A -1-1-onto-> B )

  proof
    cG
    cushgr
    wcel
    #
    cN
    cV
    wcel
    #
    wa
    #
    cA
    cB
    cF
    wf1o
    vi
    cv
    #
    cI
    cfv
    #
    cN
    csn
    #
    wceq
    #
    vi
    cI
    cdm
    #
    crab
    #
    cI
    @8
    cima
    #
    cI
    @8
    cres
    #
    wf1o
    #
    @2
    @7
    cG
    cvtx
    cfv
    #
    cpw
    c0
    csn
    cdif
    #
    cI
    wf1
    #
    @8
    @7
    wss
    #
    @11
    @0
    @14
    @1
    cI
    cG
    @12
    @12
    eqid
    ushgredgedgloop.i
    ushgrf
    #
    adantr
    @6
    vi
    @7
    ssrab2
    #
    @7
    @13
    @8
    cI
    f1ores
    sylancl
    @2
    cA
    @8
    cB
    @9
    cF
    @10
    @2
    cF
    vx
    @8
    vx
    cv
    #
    cI
    cfv
    #
    cmpt
    #
    @10
    @2
    cF
    vx
    cA
    @19
    cmpt
    @20
    ushgredgedgloop.f
    @2
    vx
    cA
    @19
    @8
    @19
    cA
    @8
    wceq
    @2
    ushgredgedgloop.a
    a1i
    #
    @2
    @18
    cA
    wcel
    wa
    @19
    eqidd
    mpteq12dva
    syl5eq
    @0
    @10
    @20
    wceq
    @1
    @0
    vx
    @7
    @13
    @8
    cI
    @0
    @14
    @7
    @13
    cI
    wf
    @16
    @7
    @13
    cI
    f1f
    syl
    @15
    @0
    @17
    a1i
    feqresmpt
    adantr
    eqtr4d
    @21
    @2
    @9
    vj
    cv
    #
    cI
    cfv
    #
    ve
    cv
    #
    wceq
    #
    vj
    @8
    wrex
    #
    ve
    cab
    #
    cB
    @2
    cI
    wfun
    #
    @15
    @9
    @27
    wceq
    @0
    @28
    @1
    @0
    cG
    ciedg
    cfv
    #
    wfun
    #
    @28
    @0
    cG
    cuhgr
    wcel
    @30
    cG
    ushgruhgr
    @29
    cG
    @29
    eqid
    uhgrfun
    syl
    #
    cI
    @29
    ushgredgedgloop.i
    funeqi
    sylibr
    adantr
    #
    @17
    vj
    ve
    @8
    cI
    dfimafn
    sylancl
    @2
    vf
    @27
    cB
    @2
    @23
    vf
    cv
    #
    wceq
    #
    vj
    @8
    wrex
    #
    @33
    cE
    wcel
    #
    @33
    @5
    wceq
    #
    wa
    #
    @33
    @27
    wcel
    @33
    cB
    wcel
    @2
    @35
    @38
    @2
    @34
    @38
    vj
    @8
    @22
    @8
    wcel
    #
    @22
    @7
    wcel
    #
    @23
    @5
    wceq
    #
    wa
    #
    @2
    @34
    @38
    wi
    @6
    @41
    vi
    @22
    @7
    @3
    @22
    wceq
    @4
    @23
    @5
    @3
    @22
    cI
    fveq2
    eqeq1d
    elrab
    #
    @2
    @42
    @34
    @38
    @2
    @42
    @34
    w3a
    #
    @36
    @37
    @44
    @36
    @33
    @29
    crn
    #
    wcel
    #
    @44
    @46
    @23
    @45
    wcel
    #
    @2
    @42
    @47
    @34
    @2
    @28
    @40
    @47
    @42
    @32
    @40
    @41
    simpl
    @28
    @40
    wa
    @23
    cI
    crn
    @45
    @22
    cI
    fvelrn
    @29
    cI
    cI
    @29
    ushgredgedgloop.i
    eqcomi
    #
    rneqi
    syl6eleqr
    syl2an
    3adant3
    @34
    @2
    @46
    @47
    wb
    #
    @42
    @49
    @33
    @23
    @33
    @23
    @45
    eleq1
    eqcoms
    3ad2ant3
    mpbird
    @2
    @42
    @36
    @46
    wb
    #
    @34
    @0
    @50
    @1
    @0
    cE
    @45
    @33
    @0
    cE
    cG
    cedg
    cfv
    #
    @45
    ushgredgedgloop.e
    @51
    @45
    wceq
    @0
    cG
    edgval
    a1i
    syl5eq
    eleq2d
    #
    adantr
    3ad2ant1
    mpbird
    @2
    @42
    @34
    @37
    @42
    @34
    @37
    wi
    #
    wi
    @2
    @41
    @53
    @40
    @34
    @41
    @37
    @23
    @33
    @5
    eqeq1
    biimpcd
    adantl
    a1i
    3imp
    jca
    3exp
    syl5bi
    rexlimdv
    @0
    @38
    @35
    wi
    @1
    @0
    @36
    @37
    @35
    @0
    @36
    @46
    @37
    @35
    wi
    #
    @52
    @0
    @46
    @22
    @29
    cfv
    #
    @33
    wceq
    #
    vj
    @29
    cdm
    #
    wrex
    #
    @54
    @0
    @29
    @57
    wfn
    #
    @46
    @58
    wb
    @0
    @30
    @59
    @31
    @30
    @59
    @29
    funfn
    biimpi
    syl
    vj
    @57
    @33
    @29
    fvelrnb
    syl
    @0
    @37
    @58
    @35
    @0
    @37
    @58
    @35
    wi
    @0
    @37
    wa
    #
    @56
    @34
    vj
    @57
    @8
    @60
    @22
    @57
    wcel
    #
    @56
    wa
    #
    @39
    @34
    wa
    @60
    @62
    wa
    #
    @39
    @34
    @63
    @42
    @39
    @63
    @40
    @41
    @62
    @40
    @60
    @61
    @40
    @56
    @61
    @40
    @57
    @7
    @22
    @29
    cI
    @48
    dmeqi
    eleq2i
    biimpi
    adantr
    adantl
    @60
    @62
    @41
    @60
    @56
    @41
    @61
    @37
    @56
    @41
    wi
    @0
    @56
    @37
    @41
    @56
    @33
    @23
    @5
    @33
    @23
    wceq
    #
    @33
    @55
    @33
    @55
    wceq
    @64
    @55
    @23
    @33
    @22
    @29
    cI
    @48
    fveq1i
    #
    eqeq2i
    biimpi
    eqcoms
    eqeq1d
    biimpcd
    adantl
    adantld
    imp
    jca
    @43
    sylibr
    @62
    @34
    @60
    @56
    @34
    @61
    @56
    @34
    @55
    @23
    @33
    @65
    eqeq1i
    biimpi
    adantl
    adantl
    jca
    ex
    reximdv2
    ex
    com23
    sylbid
    sylbid
    impd
    adantr
    impbid
    @26
    @35
    ve
    @33
    vf
    vex
    @24
    @33
    wceq
    @25
    @34
    vj
    @8
    @24
    @33
    @23
    eqeq2
    rexbidv
    elab
    @24
    @5
    wceq
    @37
    ve
    @33
    cE
    cB
    @24
    @33
    @5
    eqeq1
    ushgredgedgloop.b
    elrab2
    3bitr4g
    eqrdv
    eqtr2d
    f1oeq123d
    mpbird
end
