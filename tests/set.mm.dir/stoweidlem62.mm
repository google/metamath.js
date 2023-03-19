include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "c2.mm"
include "cdiv.mm"
include "cmul.mm"
include "crn.mm"
include "cr.mm"
include "cinf.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "wcel.mm"
include "w3a.mm"
include "caddc.mm"
include "wi.mm"
include "wceq.mm"
include "eleq1.mm"
include "3anbi3d.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvarv.mm"
include "cneg.mm"
include "csn.mm"
include "cxp.mm"
include "nfrn.mm"
include "nfcv.mm"
include "nfinf.mm"
include "eqid.mm"
include "ccmp.mm"
include "ctop.mm"
include "cmptop.mm"
include "syl.mm"
include "cle.mm"
include "ccn.mm"
include "syl6eleq.mm"
include "stoweidlem29.mm"
include "simp2d.mm"
include "stoweidlem47.mm"
include "syl5eqel.mm"
include "cc0.mm"
include "wa.mm"
include "simp3d.mm"
include "r19.21bi.mm"
include "fcnre.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "subge0d.mm"
include "mpbird.mm"
include "simpr.mm"
include "resubcld.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "breqtrrd.mm"
include "ex.mm"
include "ralrimi.mm"
include "rphalfcld.mm"
include "c1.mm"
include "c3.mm"
include "rpred.mm"
include "rehalfcld.mm"
include "3re.mm"
include "3ne0.mm"
include "rereccli.mm"
include "a1i.mm"
include "crp.mm"
include "rphalflt.mm"
include "lttrd.mm"
include "stoweidlem61.mm"
include "nfra1.mm"
include "nfan.mm"
include "rsp.mm"
include "rpcnd.mm"
include "2cnd.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan2d.mm"
include "breq2d.mm"
include "biimpd.mm"
include "sylan9r.mm"
include "reximdv.mm"
include "mpd.mm"
include "nfv.mm"
include "wf.mm"
include "3adant1r.mm"
include "adantlr.mm"
include "cuni.mm"
include "sseld.mm"
include "eleq2i.mm"
include "syl6ib.mm"
include "cioo.mm"
include "ctg.mm"
include "uniretop.mm"
include "unieqi.mm"
include "eqtr4i.mm"
include "cnf.mm"
include "syl6.mm"
include "wb.mm"
include "feq2.mm"
include "mp1i.mm"
include "sylibrd.mm"
include "simprl.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "simplrr.mm"
include "rspa.mm"
include "sylancom.mm"
include "eqbrtrd.mm"
include "stoweidlem21.mm"
include "rexlimddv.mm"

theorem stoweidlem62
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cC: class C
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cH: class H
  let cJ: class J
  let cK: class K
  let vr: setvar r
  let vq: setvar q
  let vh: setvar h
  let vk: setvar k
  assume stoweidlem62.1: |- F/_ t F
  assume stoweidlem62.2: |- F/ f ph
  assume stoweidlem62.3: |- F/ t ph
  assume stoweidlem62.4: |- H = ( t e. T |-> ( ( F ` t ) - inf ( ran F , RR , < ) ) )
  assume stoweidlem62.5: |- K = ( topGen ` ran (,) )
  assume stoweidlem62.6: |- T = U. J
  assume stoweidlem62.7: |- ( ph -> J e. Comp )
  assume stoweidlem62.8: |- C = ( J Cn K )
  assume stoweidlem62.9: |- ( ph -> A C_ C )
  assume stoweidlem62.10: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem62.11: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem62.12: |- ( ( ph /\ x e. RR ) -> ( t e. T |-> x ) e. A )
  assume stoweidlem62.13: |- ( ( ph /\ ( r e. T /\ t e. T /\ r =/= t ) ) -> E. q e. A ( q ` r ) =/= ( q ` t ) )
  assume stoweidlem62.14: |- ( ph -> F e. C )
  assume stoweidlem62.15: |- ( ph -> E e. RR+ )
  assume stoweidlem62.16: |- ( ph -> T =/= (/) )
  assume stoweidlem62.17: |- ( ph -> E < ( 1 / 3 ) )

  disjoint f g
  disjoint f t
  disjoint A f
  disjoint g t
  disjoint A g
  disjoint A t
  disjoint f q
  disjoint f r
  disjoint f x
  disjoint q r
  disjoint q t
  disjoint q x
  disjoint A q
  disjoint r t
  disjoint r x
  disjoint A r
  disjoint t x
  disjoint A x
  disjoint E f
  disjoint E g
  disjoint E t
  disjoint F f
  disjoint F g
  disjoint H f
  disjoint H g
  disjoint J f
  disjoint J r
  disjoint J t
  disjoint T f
  disjoint T g
  disjoint T t
  disjoint f ph
  disjoint g ph
  disjoint E q
  disjoint E r
  disjoint E x
  disjoint H q
  disjoint H r
  disjoint H x
  disjoint T q
  disjoint T r
  disjoint T x
  disjoint ph q
  disjoint ph r
  disjoint ph x
  disjoint K t
  disjoint F x
  disjoint f h
  disjoint g h
  disjoint h t
  disjoint A h
  disjoint h q
  disjoint h r
  disjoint h x
  disjoint E h
  disjoint F h
  disjoint H h
  disjoint J h
  disjoint T h
  disjoint h ph
  disjoint k x
  assert |- ( ph -> E. f e. A A. t e. T ( abs ` ( ( f ` t ) - ( F ` t ) ) ) < E )

  proof
    wph
    vt
    cv
    #
    vh
    cv
    #
    cfv
    #
    @0
    cH
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cE
    clt
    wbr
    #
    vt
    cT
    wral
    #
    @0
    vf
    cv
    #
    cfv
    #
    @0
    cF
    cfv
    #
    cmin
    co
    cabs
    cfv
    cE
    clt
    wbr
    vt
    cT
    wral
    vf
    cA
    wrex
    vh
    cA
    wph
    @5
    c2
    cE
    c2
    cdiv
    co
    #
    cmul
    co
    #
    clt
    wbr
    #
    vt
    cT
    wral
    #
    vh
    cA
    wrex
    @7
    vh
    cA
    wrex
    wph
    vx
    vt
    cA
    cC
    cT
    vf
    vh
    @11
    cH
    cJ
    cK
    vr
    vq
    vt
    cH
    vt
    cT
    @10
    cF
    crn
    #
    cr
    clt
    cinf
    #
    cmin
    co
    #
    cmpt
    #
    stoweidlem62.4
    vt
    cT
    @17
    nfmpt1
    nfcxfr
    stoweidlem62.3
    stoweidlem62.5
    stoweidlem62.7
    stoweidlem62.6
    stoweidlem62.16
    stoweidlem62.8
    stoweidlem62.9
    wph
    @8
    cA
    wcel
    #
    vg
    cv
    #
    cA
    wcel
    #
    w3a
    #
    vt
    cT
    @9
    @0
    @20
    cfv
    #
    caddc
    co
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    wph
    @19
    @1
    cA
    wcel
    #
    w3a
    #
    vt
    cT
    @9
    @2
    caddc
    co
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    vg
    vh
    @20
    @1
    wceq
    #
    @22
    @28
    @26
    @31
    @32
    @21
    @27
    wph
    @19
    @20
    @1
    cA
    eleq1
    3anbi3d
    #
    @32
    @25
    @30
    cA
    @32
    vt
    cT
    @24
    @29
    @32
    @23
    @2
    @9
    caddc
    @0
    @20
    @1
    fveq1
    #
    oveq2d
    mpteq2dv
    eleq1d
    imbi12d
    stoweidlem62.10
    chvarv
    @22
    vt
    cT
    @9
    @23
    cmul
    co
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    @28
    vt
    cT
    @9
    @2
    cmul
    co
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    vg
    vh
    @32
    @22
    @28
    @37
    @40
    @33
    @32
    @36
    @39
    cA
    @32
    vt
    cT
    @35
    @38
    @32
    @23
    @2
    @9
    cmul
    @34
    oveq2d
    mpteq2dv
    eleq1d
    imbi12d
    stoweidlem62.11
    chvarv
    stoweidlem62.12
    stoweidlem62.13
    wph
    cH
    @18
    cC
    stoweidlem62.4
    wph
    vt
    cC
    @16
    cT
    cF
    cT
    @16
    cneg
    csn
    cxp
    #
    cJ
    cK
    stoweidlem62.1
    vt
    @15
    cr
    clt
    vt
    cF
    stoweidlem62.1
    nfrn
    vt
    cr
    nfcv
    vt
    clt
    nfcv
    nfinf
    #
    stoweidlem62.3
    stoweidlem62.6
    @41
    eqid
    stoweidlem62.5
    wph
    cJ
    ccmp
    wcel
    cJ
    ctop
    wcel
    stoweidlem62.7
    cJ
    cmptop
    syl
    stoweidlem62.8
    stoweidlem62.14
    wph
    @16
    @15
    wcel
    #
    @16
    cr
    wcel
    #
    @16
    @10
    cle
    wbr
    #
    vt
    cT
    wral
    #
    wph
    vt
    cT
    cF
    cJ
    cK
    stoweidlem62.1
    stoweidlem62.3
    stoweidlem62.6
    stoweidlem62.5
    stoweidlem62.7
    wph
    cF
    cC
    cJ
    cK
    ccn
    co
    #
    stoweidlem62.14
    stoweidlem62.8
    syl6eleq
    stoweidlem62.16
    stoweidlem29
    #
    simp2d
    #
    stoweidlem47
    syl5eqel
    wph
    cc0
    @3
    cle
    wbr
    #
    vt
    cT
    stoweidlem62.3
    wph
    @0
    cT
    wcel
    #
    @50
    wph
    @51
    wa
    #
    cc0
    @17
    @3
    cle
    @52
    cc0
    @17
    cle
    wbr
    @45
    wph
    @45
    vt
    cT
    wph
    @43
    @44
    @46
    @48
    simp3d
    r19.21bi
    @52
    @10
    @16
    wph
    cT
    cr
    @0
    cF
    wph
    cC
    cT
    cF
    cJ
    cK
    stoweidlem62.5
    stoweidlem62.6
    stoweidlem62.8
    stoweidlem62.14
    fcnre
    #
    ffvelrnda
    #
    wph
    @44
    @51
    @49
    adantr
    #
    subge0d
    mpbird
    @52
    @51
    @17
    cr
    wcel
    @3
    @17
    wceq
    wph
    @51
    simpr
    @52
    @10
    @16
    @54
    @55
    resubcld
    vt
    cT
    @17
    cr
    cH
    stoweidlem62.4
    fvmpt2
    syl2anc
    #
    breqtrrd
    ex
    ralrimi
    wph
    cE
    stoweidlem62.15
    rphalfcld
    wph
    @11
    cE
    c1
    c3
    cdiv
    co
    #
    wph
    cE
    wph
    cE
    stoweidlem62.15
    rpred
    #
    rehalfcld
    @58
    @57
    cr
    wcel
    wph
    c3
    3re
    3ne0
    rereccli
    a1i
    wph
    cE
    crp
    wcel
    @11
    cE
    clt
    wbr
    stoweidlem62.15
    cE
    rphalflt
    syl
    stoweidlem62.17
    lttrd
    stoweidlem61
    wph
    @14
    @7
    vh
    cA
    wph
    @14
    @7
    wph
    @14
    wa
    @6
    vt
    cT
    wph
    @14
    vt
    stoweidlem62.3
    @13
    vt
    cT
    nfra1
    nfan
    @14
    @51
    @13
    wph
    @6
    @13
    vt
    cT
    rsp
    wph
    @13
    @6
    wph
    @12
    cE
    @5
    clt
    wph
    cE
    c2
    wph
    cE
    stoweidlem62.15
    rpcnd
    wph
    2cnd
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    divcan2d
    breq2d
    biimpd
    sylan9r
    ralrimi
    ex
    reximdv
    mpd
    wph
    @27
    @7
    wa
    #
    wa
    #
    vx
    vt
    cA
    @16
    cT
    vf
    vg
    cE
    cF
    vt
    cT
    @2
    @16
    caddc
    co
    #
    cmpt
    #
    @1
    vt
    cT
    @61
    nfmpt1
    vt
    @1
    nfcv
    @42
    wph
    @59
    vt
    stoweidlem62.3
    @27
    @7
    vt
    @27
    vt
    nfv
    @6
    vt
    cT
    nfra1
    nfan
    nfan
    #
    @62
    eqid
    wph
    cT
    cr
    cF
    wf
    @59
    @53
    adantr
    wph
    @44
    @59
    @49
    adantr
    wph
    @19
    @21
    @26
    @59
    stoweidlem62.10
    3adant1r
    wph
    vx
    cv
    #
    cr
    wcel
    vt
    cT
    @64
    cmpt
    cA
    wcel
    @59
    stoweidlem62.12
    adantlr
    wph
    cT
    cr
    @8
    wf
    #
    vf
    cA
    wral
    @59
    wph
    @65
    vf
    cA
    stoweidlem62.2
    wph
    @19
    cJ
    cuni
    #
    cr
    @8
    wf
    #
    @65
    wph
    @19
    @8
    @47
    wcel
    #
    @67
    wph
    @19
    @8
    cC
    wcel
    @68
    wph
    cA
    cC
    @8
    stoweidlem62.9
    sseld
    cC
    @47
    @8
    stoweidlem62.8
    eleq2i
    syl6ib
    @8
    cJ
    cK
    @66
    cr
    @66
    eqid
    cr
    cioo
    crn
    ctg
    cfv
    #
    cuni
    cK
    cuni
    uniretop
    cK
    @69
    stoweidlem62.5
    unieqi
    eqtr4i
    cnf
    syl6
    cT
    @66
    wceq
    @65
    @67
    wb
    wph
    stoweidlem62.6
    cT
    @66
    cr
    @8
    feq2
    mp1i
    sylibrd
    ralrimi
    adantr
    wph
    @27
    @7
    simprl
    @60
    @2
    @17
    cmin
    co
    #
    cabs
    cfv
    #
    cE
    clt
    wbr
    #
    vt
    cT
    @63
    @60
    @51
    @72
    @60
    @51
    wa
    @71
    @5
    cE
    clt
    wph
    @51
    @71
    @5
    wceq
    @59
    @52
    @70
    @4
    cabs
    @52
    @17
    @3
    @2
    cmin
    @52
    @3
    @17
    @56
    eqcomd
    oveq2d
    fveq2d
    adantlr
    @60
    @51
    @7
    @6
    wph
    @27
    @7
    @51
    simplrr
    @6
    vt
    cT
    rspa
    sylancom
    eqbrtrd
    ex
    ralrimi
    stoweidlem21
    rexlimddv
end
