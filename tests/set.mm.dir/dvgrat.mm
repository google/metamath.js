include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "wn.mm"
include "wnel.mm"
include "cc0.mm"
include "wbr.mm"
include "cfv.mm"
include "cabs.mm"
include "cle.mm"
include "clt.mm"
include "cz.mm"
include "cuz.mm"
include "syl6eleq.mm"
include "eluzelz.mm"
include "syl.mm"
include "uzid.mm"
include "syl6eleqr.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "eleq1d.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "wne.mm"
include "cc.mm"
include "wb.mm"
include "eleq2i.mm"
include "uztrn2.mm"
include "sylan2b.mm"
include "sylan.mm"
include "syldan.mm"
include "absgt0.mm"
include "mpbid.mm"
include "ex.mm"
include "vtocld.mm"
include "mpd.mm"
include "0red.mm"
include "abscld.mm"
include "ltnled.mm"
include "cmpt.mm"
include "adantr.mm"
include "cr.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "a1i.mm"
include "adantlr.mm"
include "eqidd.mm"
include "fvmptd.mm"
include "climabs.mm"
include "abs0.mm"
include "syl6breq.mm"
include "eqeltrd.mm"
include "c1.mm"
include "co.mm"
include "fveq2.mm"
include "imbi2d.mm"
include "leidd.mm"
include "expcom.mm"
include "ad2antrr.mm"
include "peano2uzs.mm"
include "ovex.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "chvarv.mm"
include "vtocl.mm"
include "sylan2.mm"
include "letrd.mm"
include "sylan2br.mm"
include "a2d.mm"
include "uzind4.mm"
include "impcom.mm"
include "breqtrrd.mm"
include "climlec2.mm"
include "mtand.mm"
include "eluzel2.mm"
include "serf0.mm"
include "df-nel.mm"
include "sylibr.mm"

theorem dvgrat
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vi: setvar i
  assume dvgrat.z: |- Z = ( ZZ>= ` M )
  assume dvgrat.w: |- W = ( ZZ>= ` N )
  assume dvgrat.n: |- ( ph -> N e. Z )
  assume dvgrat.f: |- ( ph -> F e. V )
  assume dvgrat.c: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )
  assume dvgrat.n0: |- ( ( ph /\ k e. W ) -> ( F ` k ) =/= 0 )
  assume dvgrat.le: |- ( ( ph /\ k e. W ) -> ( abs ` ( F ` k ) ) <_ ( abs ` ( F ` ( k + 1 ) ) ) )

  disjoint k ph
  disjoint F k
  disjoint N k
  disjoint W k
  disjoint M k
  disjoint V k
  disjoint Z k
  disjoint i k
  disjoint i ph
  disjoint F i
  disjoint N i
  disjoint W i
  assert |- ( ph -> seq M ( + , F ) e/ dom ~~> )

  proof
    wph
    caddc
    cF
    cM
    cseq
    #
    cli
    cdm
    #
    wcel
    #
    wn
    @0
    @1
    wnel
    wph
    @2
    cF
    cc0
    cli
    wbr
    #
    wph
    @3
    cN
    cF
    cfv
    #
    cabs
    cfv
    #
    cc0
    cle
    wbr
    #
    wph
    cc0
    @5
    clt
    wbr
    #
    @6
    wn
    wph
    cN
    cW
    wcel
    #
    @7
    wph
    cN
    cz
    wcel
    #
    @8
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    @9
    wph
    cN
    cZ
    @10
    dvgrat.n
    dvgrat.z
    syl6eleq
    #
    cM
    cN
    eluzelz
    syl
    #
    @9
    cN
    cN
    cuz
    cfv
    #
    cW
    cN
    uzid
    dvgrat.w
    syl6eleqr
    syl
    wph
    vk
    cv
    #
    cW
    wcel
    #
    cc0
    @15
    cF
    cfv
    #
    cabs
    cfv
    #
    clt
    wbr
    #
    wi
    @8
    @7
    wi
    vk
    cN
    cZ
    dvgrat.n
    wph
    @15
    cN
    wceq
    #
    wa
    #
    @16
    @8
    @19
    @7
    @21
    @15
    cN
    cW
    wph
    @20
    simpr
    #
    eleq1d
    @21
    @18
    @5
    cc0
    clt
    @21
    @17
    @4
    cabs
    @21
    @15
    cN
    cF
    @22
    fveq2d
    #
    fveq2d
    breq2d
    imbi12d
    wph
    @16
    @19
    wph
    @16
    wa
    #
    @17
    cc0
    wne
    #
    @19
    dvgrat.n0
    @24
    @17
    cc
    wcel
    #
    @25
    @19
    wb
    wph
    @16
    @15
    cZ
    wcel
    #
    @26
    wph
    cN
    cZ
    wcel
    #
    @16
    @27
    dvgrat.n
    @16
    @28
    @15
    @14
    wcel
    #
    @27
    cW
    @14
    @15
    dvgrat.w
    eleq2i
    #
    cM
    @15
    cN
    cZ
    dvgrat.z
    uztrn2
    sylan2b
    sylan
    dvgrat.c
    syldan
    #
    @17
    absgt0
    syl
    mpbid
    ex
    vtocld
    mpd
    wph
    cc0
    @5
    wph
    0red
    wph
    @4
    wph
    @28
    @4
    cc
    wcel
    #
    dvgrat.n
    wph
    @27
    @26
    wi
    @28
    @32
    wi
    vk
    cN
    cZ
    dvgrat.n
    @21
    @27
    @28
    @26
    @32
    @21
    @15
    cN
    cZ
    @22
    eleq1d
    @21
    @17
    @4
    cc
    @23
    eleq1d
    imbi12d
    wph
    @27
    @26
    dvgrat.c
    ex
    vtocld
    mpd
    abscld
    #
    ltnled
    mpbid
    wph
    @3
    wa
    #
    @5
    cc0
    vk
    vi
    cW
    vi
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    cmpt
    #
    cN
    cW
    dvgrat.w
    wph
    @9
    @3
    @13
    adantr
    #
    wph
    @5
    cr
    wcel
    #
    @3
    @33
    adantr
    @34
    @38
    cc0
    cabs
    cfv
    cc0
    cli
    @34
    cc0
    vk
    cF
    @38
    cN
    cvv
    cW
    dvgrat.w
    wph
    @3
    simpr
    @38
    cvv
    wcel
    @34
    vi
    cW
    @37
    cW
    @14
    cvv
    dvgrat.w
    cN
    cuz
    fvex
    eqeltri
    mptex
    a1i
    @39
    wph
    @16
    @26
    @3
    @31
    adantlr
    #
    @34
    @16
    wa
    #
    vi
    @15
    @37
    @18
    cW
    @38
    cvv
    @42
    @38
    eqidd
    @42
    @35
    @15
    wceq
    #
    wa
    #
    @36
    @17
    cabs
    @44
    @35
    @15
    cF
    @42
    @43
    simpr
    fveq2d
    fveq2d
    @34
    @16
    simpr
    @18
    cvv
    wcel
    @42
    @17
    cabs
    fvex
    a1i
    fvmptd
    #
    climabs
    abs0
    syl6breq
    @42
    @15
    @38
    cfv
    #
    @18
    cr
    @45
    @42
    @17
    @41
    abscld
    eqeltrd
    @42
    @5
    @18
    @46
    cle
    wph
    @16
    @5
    @18
    cle
    wbr
    #
    @3
    @16
    wph
    @29
    @47
    @30
    @29
    wph
    @47
    wph
    @5
    @37
    cle
    wbr
    #
    wi
    wph
    @5
    @5
    cle
    wbr
    #
    wi
    wph
    @47
    wi
    #
    wph
    @5
    @15
    c1
    caddc
    co
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    wi
    @50
    vi
    vk
    cN
    @15
    @35
    cN
    wceq
    #
    @48
    @49
    wph
    @55
    @37
    @5
    @5
    cle
    @55
    @36
    @4
    cabs
    @35
    cN
    cF
    fveq2
    fveq2d
    breq2d
    imbi2d
    @43
    @48
    @47
    wph
    @43
    @37
    @18
    @5
    cle
    @43
    @36
    @17
    cabs
    @35
    @15
    cF
    fveq2
    fveq2d
    breq2d
    imbi2d
    #
    @35
    @51
    wceq
    #
    @48
    @54
    wph
    @57
    @37
    @53
    @5
    cle
    @57
    @36
    @52
    cabs
    @35
    @51
    cF
    fveq2
    #
    fveq2d
    breq2d
    imbi2d
    @56
    wph
    @9
    @49
    wph
    @9
    wa
    @5
    wph
    @40
    @9
    @33
    adantr
    leidd
    expcom
    @29
    wph
    @47
    @54
    wph
    @29
    @47
    @54
    wi
    #
    @29
    wph
    @16
    @59
    @30
    @24
    @47
    @54
    @24
    @47
    wa
    #
    @5
    @18
    @53
    wph
    @40
    @16
    @47
    @33
    ad2antrr
    @60
    @17
    @24
    @26
    @47
    @31
    adantr
    abscld
    @60
    @52
    @24
    @52
    cc
    wcel
    #
    @47
    @16
    wph
    @51
    cW
    wcel
    #
    @61
    cN
    @15
    cW
    dvgrat.w
    peano2uzs
    wph
    @35
    cW
    wcel
    #
    wa
    #
    @36
    cc
    wcel
    #
    wi
    #
    wph
    @62
    wa
    #
    @61
    wi
    vi
    @51
    @15
    c1
    caddc
    ovex
    @57
    @64
    @67
    @65
    @61
    @57
    @63
    @62
    wph
    @35
    @51
    cW
    eleq1
    anbi2d
    @57
    @36
    @52
    cc
    @58
    eleq1d
    imbi12d
    @24
    @26
    wi
    @66
    vk
    vi
    @15
    @35
    wceq
    #
    @24
    @64
    @26
    @65
    @68
    @16
    @63
    wph
    @15
    @35
    cW
    eleq1
    anbi2d
    @68
    @17
    @36
    cc
    @15
    @35
    cF
    fveq2
    eleq1d
    imbi12d
    @31
    chvarv
    vtocl
    sylan2
    adantr
    abscld
    @24
    @47
    simpr
    @24
    @18
    @53
    cle
    wbr
    @47
    dvgrat.le
    adantr
    letrd
    ex
    sylan2br
    expcom
    a2d
    uzind4
    impcom
    sylan2b
    adantlr
    @45
    breqtrrd
    climlec2
    mtand
    wph
    @2
    wa
    vk
    cF
    cM
    cV
    cZ
    dvgrat.z
    wph
    cM
    cz
    wcel
    #
    @2
    wph
    @11
    @69
    @12
    cM
    cN
    eluzel2
    syl
    adantr
    wph
    cF
    cV
    wcel
    @2
    dvgrat.f
    adantr
    wph
    @2
    simpr
    wph
    @27
    @26
    @2
    dvgrat.c
    adantlr
    serf0
    mtand
    @0
    @1
    df-nel
    sylibr
end
