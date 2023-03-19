include "cushgr.mm"
include "wcel.mm"
include "wa.mm"
include "wf1o.mm"
include "cv.mm"
include "cfv.mm"
include "cdm.mm"
include "crab.mm"
include "cima.mm"
include "cres.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
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
include "wceq.mm"
include "a1i.mm"
include "eqidd.mm"
include "mpteq12dva.mm"
include "syl5eq.mm"
include "wf.mm"
include "f1f.mm"
include "syl.mm"
include "feqresmpt.mm"
include "eqcomd.mm"
include "eqtrd.mm"
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
include "eleq2d.mm"
include "elrab.mm"
include "w3a.mm"
include "crn.mm"
include "simpl.mm"
include "fvelrn.mm"
include "eqcomi.mm"
include "rneqi.mm"
include "eleq2i.mm"
include "syl2an.mm"
include "3adant3.mm"
include "wb.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "3ad2ant3.mm"
include "mpbird.mm"
include "cedg.mm"
include "edgval.mm"
include "3ad2ant1.mm"
include "eleq2.mm"
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
include "f1oeq123d.mm"

theorem ushgredgedg
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
  assume ushgredgedg.e: |- E = ( Edg ` G )
  assume ushgredgedg.i: |- I = ( iEdg ` G )
  assume ushgredgedg.v: |- V = ( Vtx ` G )
  assume ushgredgedg.a: |- A = { i e. dom I | N e. ( I ` i ) }
  assume ushgredgedg.b: |- B = { e e. E | N e. e }
  assume ushgredgedg.f: |- F = ( x e. A |-> ( I ` x ) )

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
    cN
    vi
    cv
    #
    cI
    cfv
    #
    wcel
    #
    vi
    cI
    cdm
    #
    crab
    #
    cI
    @7
    cima
    #
    cI
    @7
    cres
    #
    wf1o
    #
    @2
    @6
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
    @7
    @6
    wss
    #
    @10
    @0
    @13
    @1
    cI
    cG
    @11
    @11
    eqid
    ushgredgedg.i
    ushgrf
    #
    adantr
    @5
    vi
    @6
    ssrab2
    #
    @6
    @12
    @7
    cI
    f1ores
    sylancl
    @2
    cA
    @7
    cB
    @8
    cF
    @9
    @2
    cF
    vx
    @7
    vx
    cv
    #
    cI
    cfv
    #
    cmpt
    #
    @9
    @2
    cF
    vx
    cA
    @18
    cmpt
    @19
    ushgredgedg.f
    @2
    vx
    cA
    @18
    @7
    @18
    cA
    @7
    wceq
    @2
    ushgredgedg.a
    a1i
    #
    @2
    @17
    cA
    wcel
    wa
    @18
    eqidd
    mpteq12dva
    syl5eq
    @2
    @9
    @19
    @0
    @9
    @19
    wceq
    @1
    @0
    vx
    @6
    @12
    @7
    cI
    @0
    @13
    @6
    @12
    cI
    wf
    @15
    @6
    @12
    cI
    f1f
    syl
    @14
    @0
    @16
    a1i
    feqresmpt
    adantr
    eqcomd
    eqtrd
    @20
    @2
    @8
    cB
    @2
    @8
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
    @7
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
    @14
    @8
    @26
    wceq
    @0
    @27
    @1
    @0
    cG
    ciedg
    cfv
    #
    wfun
    #
    @27
    @0
    cG
    cuhgr
    wcel
    @29
    cG
    ushgruhgr
    @28
    cG
    @28
    eqid
    uhgrfun
    syl
    #
    cI
    @28
    ushgredgedg.i
    funeqi
    sylibr
    adantr
    #
    @16
    vj
    ve
    @7
    cI
    dfimafn
    sylancl
    @2
    vf
    @26
    cB
    @2
    @22
    vf
    cv
    #
    wceq
    #
    vj
    @7
    wrex
    #
    @32
    cE
    wcel
    #
    cN
    @32
    wcel
    #
    wa
    #
    @32
    @26
    wcel
    @32
    cB
    wcel
    @2
    @34
    @37
    @2
    @33
    @37
    vj
    @7
    @21
    @7
    wcel
    #
    @21
    @6
    wcel
    #
    cN
    @22
    wcel
    #
    wa
    #
    @2
    @33
    @37
    wi
    @5
    @40
    vi
    @21
    @6
    @3
    @21
    wceq
    @4
    @22
    cN
    @3
    @21
    cI
    fveq2
    eleq2d
    elrab
    #
    @2
    @41
    @33
    @37
    @2
    @41
    @33
    w3a
    #
    @35
    @36
    @43
    @35
    @32
    @28
    crn
    #
    wcel
    #
    @43
    @45
    @22
    @44
    wcel
    #
    @2
    @41
    @46
    @33
    @2
    @27
    @39
    @46
    @41
    @31
    @39
    @40
    simpl
    @27
    @39
    wa
    @22
    cI
    crn
    #
    wcel
    @46
    @21
    cI
    fvelrn
    @44
    @47
    @22
    @28
    cI
    cI
    @28
    ushgredgedg.i
    eqcomi
    #
    rneqi
    eleq2i
    sylibr
    syl2an
    3adant3
    @33
    @2
    @45
    @46
    wb
    #
    @41
    @49
    @32
    @22
    @32
    @22
    @44
    eleq1
    eqcoms
    3ad2ant3
    mpbird
    @2
    @41
    @35
    @45
    wb
    #
    @33
    @0
    @50
    @1
    @0
    cE
    @44
    @32
    @0
    cE
    cG
    cedg
    cfv
    #
    @44
    ushgredgedg.e
    @51
    @44
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
    @41
    @33
    @36
    @41
    @33
    @36
    wi
    #
    wi
    @2
    @40
    @53
    @39
    @33
    @40
    @36
    @22
    @32
    cN
    eleq2
    biimpcd
    adantl
    a1i
    3imp
    jca
    3exp
    syl5bi
    rexlimdv
    @0
    @37
    @34
    wi
    @1
    @0
    @35
    @36
    @34
    @0
    @35
    @45
    @36
    @34
    wi
    #
    @52
    @0
    @45
    @21
    @28
    cfv
    #
    @32
    wceq
    #
    vj
    @28
    cdm
    #
    wrex
    #
    @54
    @0
    @28
    @57
    wfn
    #
    @45
    @58
    wb
    @0
    @29
    @59
    @30
    @29
    @59
    @28
    funfn
    biimpi
    syl
    vj
    @57
    @32
    @28
    fvelrnb
    syl
    @0
    @36
    @58
    @34
    @0
    @36
    @58
    @34
    wi
    @0
    @36
    wa
    #
    @56
    @33
    vj
    @57
    @7
    @60
    @21
    @57
    wcel
    #
    @56
    wa
    #
    @38
    @33
    wa
    @60
    @62
    wa
    #
    @38
    @33
    @63
    @41
    @38
    @63
    @39
    @40
    @62
    @39
    @60
    @61
    @39
    @56
    @61
    @39
    @57
    @6
    @21
    @28
    cI
    @48
    dmeqi
    eleq2i
    biimpi
    adantr
    adantl
    @60
    @62
    @40
    @60
    @56
    @40
    @61
    @36
    @56
    @40
    wi
    @0
    @56
    @36
    @40
    @56
    @32
    @22
    cN
    @32
    @22
    wceq
    #
    @32
    @55
    @32
    @55
    wceq
    @64
    @55
    @22
    @32
    @21
    @28
    cI
    @48
    fveq1i
    #
    eqeq2i
    biimpi
    eqcoms
    eleq2d
    biimpcd
    adantl
    adantld
    imp
    jca
    @42
    sylibr
    @62
    @33
    @60
    @56
    @33
    @61
    @56
    @33
    @55
    @22
    @32
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
    @25
    @34
    ve
    @32
    vf
    vex
    @23
    @32
    wceq
    @24
    @33
    vj
    @7
    @23
    @32
    @22
    eqeq2
    rexbidv
    elab
    cN
    @23
    wcel
    @36
    ve
    @32
    cE
    cB
    @23
    @32
    cN
    eleq2
    ushgredgedg.b
    elrab2
    3bitr4g
    eqrdv
    eqtrd
    eqcomd
    f1oeq123d
    mpbird
end
