include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cdm.mm"
include "wral.mm"
include "clt.mm"
include "wi.mm"
include "cstrkg.mm"
include "iscgrgd.mm"
include "wcel.mm"
include "wa.mm"
include "simp2.mm"
include "3expia.mm"
include "ex.mm"
include "ralimdvva.mm"
include "breq1.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "breq2.mm"
include "oveq2d.mm"
include "cbvral2v.mm"
include "simpllr.mm"
include "simplr.mm"
include "simp-4r.mm"
include "jca31.mm"
include "simpr.mm"
include "rspc2v.mm"
include "imp.mm"
include "syl2anc.mm"
include "citv.mm"
include "eqid.mm"
include "ad3antrrr.mm"
include "wf.mm"
include "ad2antrr.mm"
include "fdm.mm"
include "syl.mm"
include "eleqtrd.mm"
include "ffvelrnd.mm"
include "adantr.mm"
include "tgcgrtriv.mm"
include "fveq2d.mm"
include "3eqtr3d.mm"
include "adantl3r.mm"
include "ad4antr.mm"
include "tgcgrcomlr.mm"
include "cr.mm"
include "wss.mm"
include "eqsstrd.mm"
include "adantllr.mm"
include "sseldd.mm"
include "lttri4d.mm"
include "mpjao3dan.mm"
include "anasss.mm"
include "ralrimivva.mm"
include "syl5bir.mm"
include "impbid.mm"
include "bitrd.mm"

theorem iscgrglt
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let c.sm: class .~
  let vi: setvar i
  let vj: setvar j
  let cG: class G
  let c.mi: class .-
  let vk: setvar k
  let vl: setvar l
  assume trgcgrg.p: |- P = ( Base ` G )
  assume trgcgrg.m: |- .- = ( dist ` G )
  assume trgcgrg.r: |- .~ = ( cgrG ` G )
  assume trgcgrg.g: |- ( ph -> G e. TarskiG )
  assume iscgrglt.d: |- ( ph -> D C_ RR )
  assume iscgrglt.a: |- ( ph -> A : D --> P )
  assume iscgrglt.b: |- ( ph -> B : D --> P )

  disjoint .- i
  disjoint .- j
  disjoint i j
  disjoint A i
  disjoint A j
  disjoint B i
  disjoint B j
  disjoint G i
  disjoint G j
  disjoint i ph
  disjoint j ph
  disjoint .- k
  disjoint .- l
  disjoint i k
  disjoint i l
  disjoint j k
  disjoint j l
  disjoint k l
  disjoint A k
  disjoint A l
  disjoint B k
  disjoint B l
  disjoint k ph
  disjoint l ph
  assert |- ( ph -> ( A .~ B <-> A. i e. dom A A. j e. dom A ( i < j -> ( ( A ` i ) .- ( A ` j ) ) = ( ( B ` i ) .- ( B ` j ) ) ) ) )

  proof
    wph
    cA
    cB
    c.sm
    wbr
    vi
    cv
    #
    cA
    cfv
    #
    vj
    cv
    #
    cA
    cfv
    #
    c.mi
    co
    #
    @0
    cB
    cfv
    #
    @2
    cB
    cfv
    #
    c.mi
    co
    #
    wceq
    #
    vj
    cA
    cdm
    #
    wral
    vi
    @9
    wral
    #
    @0
    @2
    clt
    wbr
    #
    @8
    wi
    #
    vj
    @9
    wral
    vi
    @9
    wral
    #
    wph
    cA
    cB
    cD
    cP
    c.sm
    vi
    vj
    cG
    c.mi
    cstrkg
    trgcgrg.p
    trgcgrg.m
    trgcgrg.r
    trgcgrg.g
    iscgrglt.d
    iscgrglt.a
    iscgrglt.b
    iscgrgd
    wph
    @10
    @13
    wph
    @8
    @12
    vi
    vj
    @9
    @9
    wph
    @0
    @9
    wcel
    #
    @2
    @9
    wcel
    #
    wa
    #
    wa
    #
    @8
    @12
    @17
    @8
    @11
    @8
    @17
    @8
    @11
    simp2
    3expia
    ex
    ralimdvva
    @13
    vk
    cv
    #
    vl
    cv
    #
    clt
    wbr
    #
    @18
    cA
    cfv
    #
    @19
    cA
    cfv
    #
    c.mi
    co
    #
    @18
    cB
    cfv
    #
    @19
    cB
    cfv
    #
    c.mi
    co
    #
    wceq
    #
    wi
    #
    vl
    @9
    wral
    vk
    @9
    wral
    #
    wph
    @10
    @28
    @12
    @0
    @19
    clt
    wbr
    #
    @1
    @22
    c.mi
    co
    #
    @5
    @25
    c.mi
    co
    #
    wceq
    #
    wi
    #
    vk
    vl
    vi
    vj
    @9
    @9
    @18
    @0
    wceq
    #
    @20
    @30
    @27
    @33
    @18
    @0
    @19
    clt
    breq1
    @35
    @23
    @31
    @26
    @32
    @35
    @21
    @1
    @22
    c.mi
    @18
    @0
    cA
    fveq2
    oveq1d
    @35
    @24
    @5
    @25
    c.mi
    @18
    @0
    cB
    fveq2
    oveq1d
    eqeq12d
    imbi12d
    #
    @19
    @2
    wceq
    #
    @30
    @11
    @33
    @8
    @19
    @2
    @0
    clt
    breq2
    @37
    @31
    @4
    @32
    @7
    @37
    @22
    @3
    @1
    c.mi
    @19
    @2
    cA
    fveq2
    oveq2d
    @37
    @25
    @6
    @5
    c.mi
    @19
    @2
    cB
    fveq2
    oveq2d
    eqeq12d
    imbi12d
    #
    cbvral2v
    wph
    @29
    @10
    wph
    @29
    wa
    #
    @8
    vi
    vj
    @9
    @9
    @39
    @14
    @15
    @8
    @39
    @14
    wa
    #
    @15
    wa
    #
    @11
    @8
    @0
    @2
    wceq
    #
    @2
    @0
    clt
    wbr
    #
    @41
    @11
    wa
    #
    @16
    @29
    wa
    #
    @11
    @8
    @44
    @14
    @15
    @29
    @39
    @14
    @15
    @11
    simpllr
    @40
    @15
    @11
    simplr
    wph
    @29
    @14
    @15
    @11
    simp-4r
    jca31
    @41
    @11
    simpr
    @45
    @11
    @8
    @16
    @29
    @12
    @28
    @12
    @34
    vk
    vl
    @0
    @2
    @9
    @9
    @36
    @38
    rspc2v
    imp
    imp
    syl2anc
    wph
    @29
    @14
    @15
    @42
    @8
    wph
    @14
    wa
    #
    @15
    wa
    #
    @42
    wa
    #
    @1
    @1
    c.mi
    co
    @5
    @5
    c.mi
    co
    @4
    @7
    @48
    @1
    @5
    cP
    cG
    cG
    citv
    cfv
    #
    c.mi
    trgcgrg.p
    trgcgrg.m
    @49
    eqid
    #
    wph
    cG
    cstrkg
    wcel
    #
    @14
    @15
    @42
    trgcgrg.g
    ad3antrrr
    @47
    @1
    cP
    wcel
    #
    @42
    @47
    cD
    cP
    @0
    cA
    wph
    cD
    cP
    cA
    wf
    #
    @14
    @15
    iscgrglt.a
    ad2antrr
    #
    @47
    @0
    @9
    cD
    wph
    @14
    @15
    simplr
    #
    @47
    @53
    @9
    cD
    wceq
    #
    @54
    cD
    cP
    cA
    fdm
    #
    syl
    #
    eleqtrd
    #
    ffvelrnd
    #
    adantr
    @47
    @5
    cP
    wcel
    #
    @42
    @47
    cD
    cP
    @0
    cB
    wph
    cD
    cP
    cB
    wf
    @14
    @15
    iscgrglt.b
    ad2antrr
    #
    @59
    ffvelrnd
    #
    adantr
    tgcgrtriv
    @48
    @1
    @3
    @1
    c.mi
    @48
    @0
    @2
    cA
    @47
    @42
    simpr
    #
    fveq2d
    oveq2d
    @48
    @5
    @6
    @5
    c.mi
    @48
    @0
    @2
    cB
    @64
    fveq2d
    oveq2d
    3eqtr3d
    adantl3r
    @41
    @43
    wa
    #
    @3
    @1
    @6
    @5
    cP
    cG
    @49
    c.mi
    trgcgrg.p
    trgcgrg.m
    @50
    wph
    @51
    @29
    @14
    @15
    @43
    trgcgrg.g
    ad4antr
    wph
    @29
    @14
    @15
    @43
    @3
    cP
    wcel
    #
    @47
    @66
    @43
    @47
    cD
    cP
    @2
    cA
    @54
    @47
    @2
    @9
    cD
    @46
    @15
    simpr
    @58
    eleqtrd
    #
    ffvelrnd
    adantr
    adantl3r
    wph
    @29
    @14
    @15
    @43
    @52
    @47
    @52
    @43
    @60
    adantr
    adantl3r
    wph
    @29
    @14
    @15
    @43
    @6
    cP
    wcel
    #
    @47
    @68
    @43
    @47
    cD
    cP
    @2
    cB
    @62
    @67
    ffvelrnd
    adantr
    adantl3r
    wph
    @29
    @14
    @15
    @43
    @61
    @47
    @61
    @43
    @63
    adantr
    adantl3r
    @65
    @15
    @14
    wa
    #
    @29
    wa
    #
    @43
    @3
    @1
    c.mi
    co
    #
    @6
    @5
    c.mi
    co
    #
    wceq
    #
    @65
    @15
    @14
    @29
    @40
    @15
    @43
    simplr
    @39
    @14
    @15
    @43
    simpllr
    wph
    @29
    @14
    @15
    @43
    simp-4r
    jca31
    @41
    @43
    simpr
    @70
    @43
    @73
    @69
    @29
    @43
    @73
    wi
    #
    @28
    @74
    @2
    @19
    clt
    wbr
    #
    @3
    @22
    c.mi
    co
    #
    @6
    @25
    c.mi
    co
    #
    wceq
    #
    wi
    vk
    vl
    @2
    @0
    @9
    @9
    @18
    @2
    wceq
    #
    @20
    @75
    @27
    @78
    @18
    @2
    @19
    clt
    breq1
    @79
    @23
    @76
    @26
    @77
    @79
    @21
    @3
    @22
    c.mi
    @18
    @2
    cA
    fveq2
    oveq1d
    @79
    @24
    @6
    @25
    c.mi
    @18
    @2
    cB
    fveq2
    oveq1d
    eqeq12d
    imbi12d
    @19
    @0
    wceq
    #
    @75
    @43
    @78
    @73
    @19
    @0
    @2
    clt
    breq2
    @80
    @76
    @71
    @77
    @72
    @80
    @22
    @1
    @3
    c.mi
    @19
    @0
    cA
    fveq2
    oveq2d
    @80
    @25
    @5
    @6
    c.mi
    @19
    @0
    cB
    fveq2
    oveq2d
    eqeq12d
    imbi12d
    rspc2v
    imp
    imp
    syl2anc
    tgcgrcomlr
    @41
    @0
    @2
    @41
    @9
    cr
    @0
    wph
    @9
    cr
    wss
    @29
    @14
    @15
    wph
    @9
    cD
    cr
    wph
    @53
    @56
    iscgrglt.a
    @57
    syl
    iscgrglt.d
    eqsstrd
    ad3antrrr
    #
    wph
    @14
    @15
    @14
    @29
    @55
    adantllr
    sseldd
    @41
    @9
    cr
    @2
    @81
    @40
    @15
    simpr
    sseldd
    lttri4d
    mpjao3dan
    anasss
    ralrimivva
    ex
    syl5bir
    impbid
    bitrd
end
