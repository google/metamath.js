include "cfusgr.mm"
include "wcel.mm"
include "cprime.mm"
include "wa.mm"
include "cclwwlkn.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "clwlksfclwwlk.mm"
include "cvtx.mm"
include "cword.mm"
include "chash.mm"
include "eqid.mm"
include "clwwlknbp.mm"
include "adantl.mm"
include "cc0.mm"
include "cs1.mm"
include "cconcat.mm"
include "cclwlks.mm"
include "wbr.mm"
include "wex.mm"
include "cclwwlk.mm"
include "isclwwlkn.mm"
include "cuspgr.mm"
include "c1.mm"
include "cle.mm"
include "wb.mm"
include "cusgr.mm"
include "fusgrusgr.mm"
include "usgruspgr.mm"
include "syl.mm"
include "adantr.mm"
include "simprl.mm"
include "wi.mm"
include "eleq1.mm"
include "prmnn.mm"
include "nnge1d.mm"
include "syl6bir.mm"
include "com12.mm"
include "imp.mm"
include "ciedg.mm"
include "clwlkclwwlk2.mm"
include "syl3anc.mm"
include "bicomd.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "cop.mm"
include "df-br.mm"
include "c1st.mm"
include "simpl.mm"
include "cwlks.mm"
include "ad2antlr.mm"
include "breq2.mm"
include "ad2antll.mm"
include "mpbird.mm"
include "jca.mm"
include "clwlkwlk.mm"
include "wlklenvclwlk.mm"
include "syl2im.mm"
include "impcom.mm"
include "vex.mm"
include "ovex.mm"
include "op1st.mm"
include "a1i.mm"
include "fveq2d.mm"
include "eqcom.mm"
include "biimpi.mm"
include "3eqtr4d.mm"
include "fveq2i.mm"
include "eqeq1i.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "csubstr.mm"
include "opeq2d.mm"
include "oveq2d.mm"
include "cvv.mm"
include "simpr.mm"
include "eqeq2.mm"
include "eqcoms.mm"
include "imbi2d.mm"
include "eqtrd.mm"
include "c2nd.mm"
include "opeq2i.mm"
include "oveq12i.mm"
include "oveq12d.mm"
include "op2nd.mm"
include "syl6eq.mm"
include "syl5eq.mm"
include "fvmptg.mm"
include "sylancl.mm"
include "wrdsymb1.mm"
include "s1cld.mm"
include "eqidd.mm"
include "swrdccatid.mm"
include "eqcomd.mm"
include "3eqtr4rd.mm"
include "ex.mm"
include "eqeq2d.mm"
include "rspcimedv.mm"
include "pm2.43b.mm"
include "syl5bi.mm"
include "exlimdv.mm"
include "adantrd.mm"
include "sylbid.mm"
include "impancom.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "dffo3.mm"

theorem clwlksfoclwwlk
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cN: class N
  let vc: setvar c
  let vi: setvar i
  let cW: class W
  let vx: setvar x
  let vf: setvar f
  let vw: setvar w
  assume clwlksfclwwlk.1: |- A = ( 1st ` c )
  assume clwlksfclwwlk.2: |- B = ( 2nd ` c )
  assume clwlksfclwwlk.c: |- C = { c e. ( ClWalks ` G ) | ( # ` A ) = N }
  assume clwlksfclwwlk.f: |- F = ( c e. C |-> ( B substr <. 0 , ( # ` A ) >. ) )

  disjoint G c
  disjoint N c
  disjoint C c
  disjoint F c
  disjoint A i
  disjoint B i
  disjoint G i
  disjoint c i
  disjoint W c
  disjoint C i
  disjoint G x
  disjoint i x
  disjoint N i
  disjoint C f
  disjoint C w
  disjoint f w
  disjoint F f
  disjoint F w
  disjoint c f
  disjoint c w
  disjoint G f
  disjoint G w
  disjoint N f
  disjoint N w
  assert |- ( ( G e. FinUSGraph /\ N e. Prime ) -> F : C -onto-> ( N ClWWalksN G ) )

  proof
    cG
    cfusgr
    wcel
    #
    cN
    cprime
    wcel
    #
    wa
    #
    cC
    cN
    cG
    cclwwlkn
    co
    #
    cF
    wf
    vw
    cv
    #
    vc
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vc
    cC
    wrex
    #
    vw
    @3
    wral
    cC
    @3
    cF
    wfo
    cA
    cB
    cC
    cF
    cG
    cN
    vc
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlksfclwwlk.c
    clwlksfclwwlk.f
    clwlksfclwwlk
    @2
    @8
    vw
    @3
    @2
    @4
    @3
    wcel
    #
    wa
    @4
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    @4
    chash
    cfv
    #
    cN
    wceq
    #
    wa
    #
    @8
    @9
    @15
    @2
    cG
    cN
    @10
    @4
    @10
    eqid
    #
    clwwlknbp
    adantl
    @2
    @15
    @9
    @8
    @2
    @15
    wa
    #
    @9
    vf
    cv
    #
    @4
    cc0
    @4
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    cG
    cclwlks
    cfv
    #
    wbr
    #
    vf
    wex
    #
    @14
    wa
    #
    @8
    @9
    @4
    cG
    cclwwlk
    cfv
    wcel
    #
    @14
    wa
    @17
    @25
    cG
    cN
    @4
    isclwwlkn
    @17
    @26
    @24
    @14
    @17
    @24
    @26
    @17
    cG
    cuspgr
    wcel
    #
    @12
    c1
    @13
    cle
    wbr
    #
    @24
    @26
    wb
    @2
    @27
    @15
    @0
    @27
    @1
    @0
    cG
    cusgr
    wcel
    @27
    cG
    fusgrusgr
    cG
    usgruspgr
    syl
    adantr
    adantr
    @2
    @12
    @14
    simprl
    #
    @2
    @15
    @28
    @1
    @15
    @28
    wi
    @0
    @15
    @1
    @28
    @14
    @1
    @28
    wi
    @12
    @14
    @1
    @13
    cprime
    wcel
    #
    @28
    @13
    cN
    cprime
    eleq1
    @30
    @13
    @13
    prmnn
    nnge1d
    syl6bir
    adantl
    com12
    adantl
    imp
    @4
    vf
    cG
    ciedg
    cfv
    #
    cG
    @10
    @16
    @31
    eqid
    clwlkclwwlk2
    syl3anc
    bicomd
    anbi1d
    syl5bb
    @17
    @24
    @8
    @14
    @17
    @23
    @8
    vf
    @23
    @18
    @21
    cop
    #
    @22
    wcel
    #
    @17
    @8
    @18
    @21
    @22
    df-br
    @17
    @33
    @8
    @33
    @17
    @33
    @8
    wi
    @33
    @17
    wa
    #
    @7
    @33
    vc
    @32
    cC
    @34
    @33
    @32
    c1st
    cfv
    #
    chash
    cfv
    #
    cN
    wceq
    #
    @32
    cC
    wcel
    #
    @33
    @17
    simpl
    @34
    @18
    chash
    cfv
    #
    @13
    @36
    cN
    @17
    @33
    @39
    @13
    wceq
    #
    @17
    @12
    @28
    wa
    #
    @33
    @32
    cG
    cwlks
    cfv
    wcel
    @40
    @17
    @12
    @28
    @29
    @17
    @28
    c1
    cN
    cle
    wbr
    #
    @1
    @42
    @0
    @15
    @1
    cN
    cN
    prmnn
    nnge1d
    ad2antlr
    @14
    @28
    @42
    wb
    @2
    @12
    @13
    cN
    c1
    cle
    breq2
    ad2antll
    mpbird
    jca
    #
    cG
    @32
    clwlkwlk
    @18
    cG
    @4
    wlklenvclwlk
    syl2im
    #
    impcom
    #
    @17
    @36
    @39
    wceq
    @33
    @17
    @35
    @18
    chash
    @35
    @18
    wceq
    #
    @17
    @18
    @21
    vf
    vex
    #
    @4
    @20
    cconcat
    ovex
    #
    op1st
    #
    a1i
    fveq2d
    adantl
    @17
    cN
    @13
    wceq
    #
    @33
    @14
    @50
    @2
    @12
    @14
    @50
    @13
    cN
    eqcom
    biimpi
    ad2antll
    adantl
    3eqtr4d
    cA
    chash
    cfv
    #
    cN
    wceq
    #
    @37
    vc
    @32
    @22
    cC
    @52
    @5
    c1st
    cfv
    #
    chash
    cfv
    #
    cN
    wceq
    #
    @5
    @32
    wceq
    #
    @37
    @51
    @54
    cN
    cA
    @53
    chash
    clwlksfclwwlk.1
    fveq2i
    #
    eqeq1i
    #
    @56
    @54
    @36
    cN
    @56
    @53
    @35
    chash
    @5
    @32
    c1st
    fveq2
    fveq2d
    #
    eqeq1d
    syl5bb
    clwlksfclwwlk.c
    elrab2
    sylanbrc
    @34
    @56
    wa
    @33
    @7
    wi
    #
    @33
    @4
    @32
    cF
    cfv
    #
    wceq
    #
    wi
    #
    @34
    @63
    @56
    @34
    @33
    @62
    @34
    @33
    wa
    #
    @21
    cc0
    @39
    cop
    #
    csubstr
    co
    #
    @21
    cc0
    @13
    cop
    #
    csubstr
    co
    #
    @61
    @4
    @64
    @65
    @67
    @21
    csubstr
    @64
    @39
    @13
    cc0
    @34
    @40
    @33
    @45
    adantr
    opeq2d
    oveq2d
    @64
    @38
    @66
    cvv
    wcel
    @61
    @66
    wceq
    @64
    @33
    @39
    cN
    wceq
    #
    @38
    @34
    @33
    simpr
    @34
    @33
    @69
    @34
    @33
    @69
    wi
    #
    @33
    @40
    wi
    #
    @17
    @71
    @33
    @44
    adantl
    @17
    @70
    @71
    wb
    #
    @33
    @14
    @72
    @2
    @12
    @14
    @69
    @40
    @33
    @69
    @40
    wb
    cN
    @13
    cN
    @13
    @39
    eqeq2
    eqcoms
    imbi2d
    ad2antll
    adantl
    mpbird
    imp
    @52
    @69
    vc
    @32
    @22
    cC
    @52
    @55
    @56
    @69
    @58
    @56
    @54
    @39
    cN
    @56
    @54
    @36
    @39
    @59
    @56
    @35
    @18
    chash
    @46
    @56
    @49
    a1i
    fveq2d
    eqtrd
    eqeq1d
    syl5bb
    clwlksfclwwlk.c
    elrab2
    sylanbrc
    @21
    @65
    csubstr
    ovex
    vc
    @32
    cB
    cc0
    @51
    cop
    #
    csubstr
    co
    #
    @66
    cC
    cvv
    cF
    @56
    @74
    @5
    c2nd
    cfv
    #
    cc0
    @54
    cop
    #
    csubstr
    co
    #
    @66
    cB
    @75
    @73
    @76
    csubstr
    clwlksfclwwlk.2
    @51
    @54
    cc0
    @57
    opeq2i
    oveq12i
    @56
    @77
    @32
    c2nd
    cfv
    #
    cc0
    @36
    cop
    #
    csubstr
    co
    @66
    @56
    @75
    @78
    @76
    @79
    csubstr
    @5
    @32
    c2nd
    fveq2
    @56
    @54
    @36
    cc0
    @59
    opeq2d
    oveq12d
    @78
    @21
    @79
    @65
    csubstr
    @18
    @21
    @47
    @48
    op2nd
    @36
    @39
    cc0
    @35
    @18
    chash
    @49
    fveq2i
    opeq2i
    oveq12i
    syl6eq
    syl5eq
    clwlksfclwwlk.f
    fvmptg
    sylancl
    @64
    @41
    @4
    @68
    wceq
    @17
    @41
    @33
    @33
    @43
    ad2antlr
    @41
    @68
    @4
    @41
    @12
    @20
    @11
    wcel
    @13
    @13
    wceq
    @68
    @4
    wceq
    @12
    @28
    simpl
    @41
    @19
    @10
    @10
    @4
    wrdsymb1
    s1cld
    @41
    @13
    eqidd
    @4
    @20
    @13
    @10
    swrdccatid
    syl3anc
    eqcomd
    syl
    3eqtr4rd
    ex
    adantr
    @56
    @60
    @63
    wb
    @34
    @56
    @7
    @62
    @33
    @56
    @6
    @61
    @4
    @5
    @32
    cF
    fveq2
    eqeq2d
    imbi2d
    adantl
    mpbird
    rspcimedv
    ex
    pm2.43b
    syl5bi
    exlimdv
    adantrd
    sylbid
    impancom
    mpd
    ralrimiva
    vc
    vw
    cC
    @3
    cF
    dffo3
    sylanbrc
end
