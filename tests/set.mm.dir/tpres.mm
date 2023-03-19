include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cxp.mm"
include "cin.mm"
include "cop.mm"
include "cpr.mm"
include "df-res.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "elin.mm"
include "wceq.mm"
include "wex.mm"
include "elxp.mm"
include "anbi2i.mm"
include "ctp.mm"
include "wi.mm"
include "eleq2d.mm"
include "wo.mm"
include "w3o.mm"
include "vex.mm"
include "eltp.mm"
include "wne.mm"
include "eldifsn.mm"
include "wb.mm"
include "eqeq1.mm"
include "adantl.mm"
include "opth.mm"
include "eqneqall.mm"
include "com12.mm"
include "impd.mm"
include "syl5bi.mm"
include "adantr.mm"
include "sylbid.mm"
include "ex.mm"
include "sylbi.mm"
include "impcom.mm"
include "exlimdvv.mm"
include "orc.mm"
include "a1d.mm"
include "olc.mm"
include "3jaoi.mm"
include "elpr.mm"
include "syl6ibr.mm"
include "expd.mm"
include "3mix2.mm"
include "3mix3.mm"
include "jaoi.mm"
include "syl6bb.mm"
include "mpbird.mm"
include "elex.mm"
include "syl.mm"
include "jca31.mm"
include "anim2i.mm"
include "opeq12.mm"
include "eqeq2d.mm"
include "eleq1.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "bi2anan9.mm"
include "spc2egv.mm"
include "syl2anc.mm"
include "mpd.mm"
include "jaoian.mm"
include "anbi1i.mm"
include "2exbii.mm"
include "sylibr.mm"
include "jca.mm"
include "impbid.mm"
include "syl5bb.mm"
include "eqrdv.mm"
include "syl5eq.mm"

theorem tpres
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let cE: class E
  let cF: class F
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  assume tpres.t: |- ( ph -> T = { <. A , D >. , <. B , E >. , <. C , F >. } )
  assume tpres.b: |- ( ph -> B e. V )
  assume tpres.c: |- ( ph -> C e. V )
  assume tpres.e: |- ( ph -> E e. V )
  assume tpres.f: |- ( ph -> F e. V )
  assume tpres.1: |- ( ph -> B =/= A )
  assume tpres.2: |- ( ph -> C =/= A )


  assert |- ( ph -> ( T |` ( _V \ { A } ) ) = { <. B , E >. , <. C , F >. } )

  proof
    wph
    cT
    cvv
    cA
    csn
    cdif
    #
    cres
    cT
    @0
    cvv
    cxp
    #
    cin
    #
    cB
    cE
    cop
    #
    cC
    cF
    cop
    #
    cpr
    #
    cT
    @0
    df-res
    wph
    vx
    @2
    @5
    vx
    cv
    #
    @2
    wcel
    @6
    cT
    wcel
    #
    @6
    @1
    wcel
    #
    wa
    #
    wph
    @6
    @5
    wcel
    #
    @6
    cT
    @1
    elin
    @9
    @7
    @6
    va
    cv
    #
    vb
    cv
    #
    cop
    #
    wceq
    #
    @11
    @0
    wcel
    #
    @12
    cvv
    wcel
    #
    wa
    #
    wa
    #
    vb
    wex
    va
    wex
    #
    wa
    #
    wph
    @10
    @8
    @19
    @7
    va
    vb
    @6
    @0
    cvv
    elxp
    anbi2i
    wph
    @20
    @10
    wph
    @7
    @19
    @10
    wph
    @7
    @6
    cA
    cD
    cop
    #
    @3
    @4
    ctp
    #
    wcel
    #
    @19
    @10
    wi
    #
    wph
    cT
    @22
    @6
    tpres.t
    eleq2d
    #
    @23
    wph
    @24
    @23
    wph
    @19
    @10
    @23
    wph
    @19
    wa
    #
    @6
    @3
    wceq
    #
    @6
    @4
    wceq
    #
    wo
    #
    @10
    @23
    @6
    @21
    wceq
    #
    @27
    @28
    w3o
    #
    @26
    @29
    wi
    #
    @6
    @21
    @3
    @4
    vx
    vex
    #
    eltp
    #
    @30
    @32
    @27
    @28
    @30
    wph
    @19
    @29
    @30
    wph
    @19
    @29
    wi
    @30
    wph
    wa
    #
    @18
    @29
    va
    vb
    @18
    @35
    @29
    @17
    @14
    @35
    @29
    wi
    #
    @15
    @14
    @36
    wi
    #
    @16
    @15
    @11
    cvv
    wcel
    #
    @11
    cA
    wne
    #
    wa
    #
    @37
    @11
    cvv
    cA
    eldifsn
    #
    @39
    @37
    @38
    @39
    @14
    @36
    @39
    @14
    wa
    #
    @30
    wph
    @29
    @42
    @30
    @13
    @21
    wceq
    #
    wph
    @29
    wi
    #
    @14
    @30
    @43
    wb
    @39
    @6
    @13
    @21
    eqeq1
    adantl
    @39
    @43
    @44
    wi
    @14
    @43
    @11
    cA
    wceq
    #
    @12
    cD
    wceq
    #
    wa
    @39
    @44
    @11
    @12
    cA
    cD
    va
    vex
    vb
    vex
    opth
    @39
    @45
    @46
    @44
    @45
    @39
    @46
    @44
    wi
    #
    @47
    @11
    cA
    eqneqall
    com12
    impd
    syl5bi
    adantr
    sylbid
    impd
    ex
    adantl
    sylbi
    adantr
    impcom
    com12
    exlimdvv
    ex
    impd
    @27
    @29
    @26
    @27
    @28
    orc
    a1d
    @28
    @29
    @26
    @28
    @27
    olc
    a1d
    3jaoi
    sylbi
    @6
    @3
    @4
    @33
    elpr
    #
    syl6ibr
    expd
    com12
    sylbid
    impd
    @10
    wph
    @20
    @10
    @29
    wph
    @20
    wi
    @48
    @29
    wph
    @20
    @29
    wph
    wa
    #
    @7
    @19
    @49
    @7
    @31
    @29
    @31
    wph
    @27
    @31
    @28
    @27
    @30
    @28
    3mix2
    @28
    @30
    @27
    3mix3
    jaoi
    adantr
    wph
    @7
    @31
    wb
    @29
    wph
    @7
    @23
    @31
    @25
    @34
    syl6bb
    adantl
    mpbird
    @49
    @14
    @40
    @16
    wa
    #
    wa
    #
    vb
    wex
    va
    wex
    #
    @19
    @27
    wph
    @52
    @28
    @27
    wph
    wa
    @27
    cB
    cvv
    wcel
    #
    cB
    cA
    wne
    #
    wa
    #
    cE
    cvv
    wcel
    #
    wa
    #
    wa
    #
    @52
    wph
    @57
    @27
    wph
    @53
    @54
    @56
    wph
    cB
    cV
    wcel
    #
    @53
    tpres.b
    cB
    cV
    elex
    syl
    tpres.1
    wph
    cE
    cV
    wcel
    #
    @56
    tpres.e
    cE
    cV
    elex
    syl
    jca31
    anim2i
    wph
    @58
    @52
    wi
    #
    @27
    wph
    @59
    @60
    @61
    tpres.b
    tpres.e
    @51
    @58
    va
    vb
    cB
    cE
    cV
    cV
    @11
    cB
    wceq
    #
    @12
    cE
    wceq
    #
    wa
    #
    @14
    @27
    @50
    @57
    @64
    @13
    @3
    @6
    @11
    @12
    cB
    cE
    opeq12
    eqeq2d
    @62
    @40
    @55
    @63
    @16
    @56
    @62
    @38
    @53
    @39
    @54
    @11
    cB
    cvv
    eleq1
    @11
    cB
    cA
    neeq1
    anbi12d
    @12
    cE
    cvv
    eleq1
    bi2anan9
    anbi12d
    spc2egv
    syl2anc
    adantl
    mpd
    @28
    wph
    wa
    @28
    cC
    cvv
    wcel
    #
    cC
    cA
    wne
    #
    wa
    #
    cF
    cvv
    wcel
    #
    wa
    #
    wa
    #
    @52
    wph
    @69
    @28
    wph
    @65
    @66
    @68
    wph
    cC
    cV
    wcel
    #
    @65
    tpres.c
    cC
    cV
    elex
    syl
    tpres.2
    wph
    cF
    cV
    wcel
    #
    @68
    tpres.f
    cF
    cV
    elex
    syl
    jca31
    anim2i
    wph
    @70
    @52
    wi
    #
    @28
    wph
    @71
    @72
    @73
    tpres.c
    tpres.f
    @51
    @70
    va
    vb
    cC
    cF
    cV
    cV
    @11
    cC
    wceq
    #
    @12
    cF
    wceq
    #
    wa
    #
    @14
    @28
    @50
    @69
    @76
    @13
    @4
    @6
    @11
    @12
    cC
    cF
    opeq12
    eqeq2d
    @74
    @40
    @67
    @75
    @16
    @68
    @74
    @38
    @65
    @39
    @66
    @11
    cC
    cvv
    eleq1
    @11
    cC
    cA
    neeq1
    anbi12d
    @12
    cF
    cvv
    eleq1
    bi2anan9
    anbi12d
    spc2egv
    syl2anc
    adantl
    mpd
    jaoian
    @18
    @51
    va
    vb
    @17
    @50
    @14
    @15
    @40
    @16
    @41
    anbi1i
    anbi2i
    2exbii
    sylibr
    jca
    ex
    sylbi
    com12
    impbid
    syl5bb
    syl5bb
    eqrdv
    syl5eq
end
