include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wex.mm"
include "n0.mm"
include "sylib.mm"
include "c1st.mm"
include "ccom.mm"
include "cn.mm"
include "csn.mm"
include "cxp.mm"
include "c1.mm"
include "cseq.mm"
include "cmopn.mm"
include "cms.mm"
include "adantr.mm"
include "crp.mm"
include "clt.mm"
include "wbr.mm"
include "wf.mm"
include "co.mm"
include "cmul.mm"
include "cle.mm"
include "adantlr.mm"
include "eqid.mm"
include "simpr.mm"
include "bfplem2.mm"
include "exlimddv.mm"
include "cc0.mm"
include "cmin.mm"
include "oveq12.mm"
include "adantl.mm"
include "eqbrtrrd.mm"
include "cme.mm"
include "cr.mm"
include "cmetmet.mm"
include "syl.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "simplrr.mm"
include "metcl.mm"
include "syl3anc.mm"
include "rpred.mm"
include "remulcld.mm"
include "suble0d.mm"
include "mpbird.mm"
include "1cnd.mm"
include "recnd.mm"
include "subdird.mm"
include "mulid2d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "1re.mm"
include "resubcl.mm"
include "sylancr.mm"
include "mul01d.mm"
include "3brtr4d.mm"
include "wb.mm"
include "0red.mm"
include "posdif.mm"
include "sylancl.mm"
include "mpbid.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "metge0.mm"
include "0re.mm"
include "letri3.mm"
include "mpbir2and.mm"
include "meteq0.mm"
include "ex.mm"
include "ralrimivva.mm"
include "fveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "anbi1d.mm"
include "equequ1.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "cbvralv.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem bfp
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cF: class F
  let cK: class K
  let cX: class X
  let vj: setvar j
  let vk: setvar k
  let cG: class G
  let cJ: class J
  let vw: setvar w
  let cA: class A
  assume bfp.2: |- ( ph -> D e. ( CMet ` X ) )
  assume bfp.3: |- ( ph -> X =/= (/) )
  assume bfp.4: |- ( ph -> K e. RR+ )
  assume bfp.5: |- ( ph -> K < 1 )
  assume bfp.6: |- ( ph -> F : X --> X )
  assume bfp.7: |- ( ( ph /\ ( x e. X /\ y e. X ) ) -> ( ( F ` x ) D ( F ` y ) ) <_ ( K x. ( x D y ) ) )

  disjoint x y
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint ph x
  disjoint ph y
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint K x
  disjoint K y
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint j k
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint D j
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint D k
  disjoint G j
  disjoint G k
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint J j
  disjoint J k
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint j w
  disjoint j ph
  disjoint k w
  disjoint k ph
  disjoint w x
  disjoint w y
  disjoint ph w
  disjoint A j
  disjoint A k
  disjoint F j
  disjoint F k
  disjoint w z
  disjoint F w
  disjoint K j
  disjoint K k
  disjoint X j
  disjoint X k
  disjoint X w
  assert |- ( ph -> E! z e. X ( F ` z ) = z )

  proof
    wph
    vz
    cv
    #
    cF
    cfv
    #
    @0
    wceq
    #
    vz
    cX
    wrex
    #
    @2
    vy
    cv
    #
    cF
    cfv
    #
    @4
    wceq
    #
    wa
    #
    vz
    vy
    weq
    #
    wi
    #
    vy
    cX
    wral
    #
    vz
    cX
    wral
    #
    @2
    vz
    cX
    wreu
    wph
    vw
    cv
    #
    cX
    wcel
    #
    @3
    vw
    wph
    cX
    c0
    wne
    #
    @13
    vw
    wex
    bfp.3
    vw
    cX
    n0
    sylib
    wph
    @13
    wa
    vx
    vy
    vz
    @12
    cD
    cF
    cF
    c1st
    ccom
    cn
    @12
    csn
    cxp
    c1
    cseq
    #
    cD
    cmopn
    cfv
    #
    cK
    cX
    wph
    cD
    cX
    cms
    cfv
    wcel
    #
    @13
    bfp.2
    adantr
    wph
    @14
    @13
    bfp.3
    adantr
    wph
    cK
    crp
    wcel
    @13
    bfp.4
    adantr
    wph
    cK
    c1
    clt
    wbr
    #
    @13
    bfp.5
    adantr
    wph
    cX
    cX
    cF
    wf
    @13
    bfp.6
    adantr
    wph
    vx
    cv
    #
    cX
    wcel
    #
    @4
    cX
    wcel
    #
    wa
    #
    @19
    cF
    cfv
    #
    @5
    cD
    co
    #
    cK
    @19
    @4
    cD
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    @13
    bfp.7
    adantlr
    @16
    eqid
    wph
    @13
    simpr
    @15
    eqid
    bfplem2
    exlimddv
    wph
    @23
    @19
    wceq
    #
    @6
    wa
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    @11
    wph
    @31
    vx
    vy
    cX
    cX
    wph
    @22
    wa
    #
    @29
    @30
    @33
    @29
    wa
    #
    @25
    cc0
    wceq
    #
    @30
    @34
    @35
    @25
    cc0
    cle
    wbr
    #
    cc0
    @25
    cle
    wbr
    #
    @34
    @36
    c1
    cK
    cmin
    co
    #
    @25
    cmul
    co
    #
    @38
    cc0
    cmul
    co
    #
    cle
    wbr
    #
    @34
    @25
    @26
    cmin
    co
    #
    cc0
    @39
    @40
    cle
    @34
    @42
    cc0
    cle
    wbr
    @25
    @26
    cle
    wbr
    @34
    @24
    @25
    @26
    cle
    @29
    @24
    @25
    wceq
    @33
    @23
    @19
    @5
    @4
    cD
    oveq12
    adantl
    @33
    @27
    @29
    bfp.7
    adantr
    eqbrtrrd
    @34
    @25
    @26
    @34
    cD
    cX
    cme
    cfv
    wcel
    #
    @20
    @21
    @25
    cr
    wcel
    #
    wph
    @43
    @22
    @29
    wph
    @17
    @43
    bfp.2
    cD
    cX
    cmetmet
    syl
    ad2antrr
    #
    wph
    @20
    @21
    @29
    simplrl
    #
    wph
    @20
    @21
    @29
    simplrr
    #
    @19
    @4
    cD
    cX
    metcl
    syl3anc
    #
    @34
    cK
    @25
    wph
    cK
    cr
    wcel
    #
    @22
    @29
    wph
    cK
    bfp.4
    rpred
    #
    ad2antrr
    #
    @48
    remulcld
    suble0d
    mpbird
    @34
    @39
    c1
    @25
    cmul
    co
    #
    @26
    cmin
    co
    @42
    @34
    c1
    cK
    @25
    @34
    1cnd
    @34
    cK
    @51
    recnd
    @34
    @25
    @48
    recnd
    #
    subdird
    @34
    @52
    @25
    @26
    cmin
    @34
    @25
    @53
    mulid2d
    oveq1d
    eqtrd
    @34
    @38
    @34
    @38
    wph
    @38
    cr
    wcel
    #
    @22
    @29
    wph
    c1
    cr
    wcel
    #
    @49
    @54
    1re
    @50
    c1
    cK
    resubcl
    sylancr
    ad2antrr
    #
    recnd
    mul01d
    3brtr4d
    @34
    @44
    cc0
    cr
    wcel
    #
    @54
    cc0
    @38
    clt
    wbr
    #
    @36
    @41
    wb
    @48
    @34
    0red
    @56
    wph
    @58
    @22
    @29
    wph
    @18
    @58
    bfp.5
    wph
    @49
    @55
    @18
    @58
    wb
    @50
    1re
    cK
    c1
    posdif
    sylancl
    mpbid
    ad2antrr
    @25
    cc0
    @38
    lemul2
    syl112anc
    mpbird
    @34
    @43
    @20
    @21
    @37
    @45
    @46
    @47
    @19
    @4
    cD
    cX
    metge0
    syl3anc
    @34
    @44
    @57
    @35
    @36
    @37
    wa
    wb
    @48
    0re
    @25
    cc0
    letri3
    sylancl
    mpbir2and
    @34
    @43
    @20
    @21
    @35
    @30
    wb
    @45
    @46
    @47
    @19
    @4
    cD
    cX
    meteq0
    syl3anc
    mpbid
    ex
    ralrimivva
    @32
    @10
    vx
    vz
    cX
    vx
    vz
    weq
    #
    @31
    @9
    vy
    cX
    @59
    @29
    @7
    @30
    @8
    @59
    @28
    @2
    @6
    @59
    @23
    @1
    @19
    @0
    @19
    @0
    cF
    fveq2
    @59
    id
    eqeq12d
    anbi1d
    vx
    vz
    vy
    equequ1
    imbi12d
    ralbidv
    cbvralv
    sylib
    @2
    @6
    vz
    vy
    cX
    @8
    @1
    @5
    @0
    @4
    @0
    @4
    cF
    fveq2
    @8
    id
    eqeq12d
    reu4
    sylanbrc
end
