include "csu.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "cfz.mm"
include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "fzfid.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "dvdsssfz1.mm"
include "syl.mm"
include "syl5eqss.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "fsumcl.mm"
include "fsummulc1.mm"
include "wa.mm"
include "adantr.mm"
include "cc.mm"
include "adantlr.mm"
include "fsummulc2.mm"
include "wceq.mm"
include "anassrs.mm"
include "sumeq2dv.mm"
include "eqtrd.mm"
include "cxp.mm"
include "cfv.mm"
include "csb.mm"
include "cop.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "csbeq1d.mm"
include "ovex.mm"
include "csbie.mm"
include "syl6eq.mm"
include "adantrr.mm"
include "adantrl.mm"
include "mulcld.mm"
include "eqeltrrd.mm"
include "fsumxp.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvsumi.mm"
include "cres.mm"
include "csbeq1.mm"
include "xpfi.mm"
include "dvdsmulf1o.mm"
include "fvres.mm"
include "adantl.mm"
include "wral.mm"
include "ralrimivva.mm"
include "eleq1d.mm"
include "ralxp.mm"
include "sylibr.mm"
include "cima.mm"
include "wfn.mm"
include "wb.mm"
include "wf.mm"
include "ax-mulf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "nnsscn.mm"
include "sstri.mm"
include "xpss12.mm"
include "mp2an.mm"
include "ralima.mm"
include "crn.mm"
include "df-ima.mm"
include "wf1o.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "syl5eq.mm"
include "raleqdv.mm"
include "syl5bbr.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "fsumf1o.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"

theorem fsumdvdsmul
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vz: setvar z
  let vu: setvar u
  let vm: setvar m
  let vn: setvar n
  let vv: setvar v
  let vw: setvar w
  assume dvdsmulf1o.1: |- ( ph -> M e. NN )
  assume dvdsmulf1o.2: |- ( ph -> N e. NN )
  assume dvdsmulf1o.3: |- ( ph -> ( M gcd N ) = 1 )
  assume dvdsmulf1o.x: |- X = { x e. NN | x || M }
  assume dvdsmulf1o.y: |- Y = { x e. NN | x || N }
  assume dvdsmulf1o.z: |- Z = { x e. NN | x || ( M x. N ) }
  assume fsumdvdsmul.4: |- ( ( ph /\ j e. X ) -> A e. CC )
  assume fsumdvdsmul.5: |- ( ( ph /\ k e. Y ) -> B e. CC )
  assume fsumdvdsmul.6: |- ( ( ph /\ ( j e. X /\ k e. Y ) ) -> ( A x. B ) = D )
  assume fsumdvdsmul.7: |- ( i = ( j x. k ) -> C = D )

  disjoint A k
  disjoint D i
  disjoint M x
  disjoint N x
  disjoint i j
  disjoint i k
  disjoint X i
  disjoint j k
  disjoint X j
  disjoint X k
  disjoint B j
  disjoint C j
  disjoint C k
  disjoint Y i
  disjoint Y j
  disjoint Y k
  disjoint Z i
  disjoint Z j
  disjoint i x
  disjoint j x
  disjoint k x
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint i z
  disjoint D z
  disjoint u x
  disjoint M u
  disjoint N u
  disjoint i m
  disjoint i n
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint j m
  disjoint j n
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j z
  disjoint k m
  disjoint k n
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k z
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m z
  disjoint X m
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n z
  disjoint X n
  disjoint u v
  disjoint u w
  disjoint u z
  disjoint X u
  disjoint v w
  disjoint v z
  disjoint X v
  disjoint w z
  disjoint X w
  disjoint X z
  disjoint C w
  disjoint C z
  disjoint Y m
  disjoint Y n
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y z
  disjoint Z u
  disjoint Z w
  disjoint Z z
  disjoint m x
  disjoint n x
  disjoint w x
  disjoint x z
  disjoint m ph
  disjoint n ph
  disjoint ph w
  disjoint ph z
  assert |- ( ph -> ( sum_ j e. X A x. sum_ k e. Y B ) = sum_ i e. Z C )

  proof
    wph
    cX
    cA
    vj
    csu
    cY
    cB
    vk
    csu
    #
    cmul
    co
    cX
    cA
    @0
    cmul
    co
    #
    vj
    csu
    cX
    cY
    cD
    vk
    csu
    #
    vj
    csu
    #
    cZ
    cC
    vi
    csu
    #
    wph
    cX
    cA
    @0
    vj
    wph
    c1
    cM
    cfz
    co
    #
    cfn
    wcel
    cX
    @5
    wss
    cX
    cfn
    wcel
    #
    wph
    c1
    cM
    fzfid
    wph
    cX
    vx
    cv
    #
    cM
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    @5
    dvdsmulf1o.x
    wph
    cM
    cn
    wcel
    @9
    @5
    wss
    dvdsmulf1o.1
    cM
    vx
    dvdsssfz1
    syl
    syl5eqss
    @5
    cX
    ssfi
    syl2anc
    #
    wph
    cY
    cB
    vk
    wph
    c1
    cN
    cfz
    co
    #
    cfn
    wcel
    cY
    @11
    wss
    cY
    cfn
    wcel
    #
    wph
    c1
    cN
    fzfid
    wph
    cY
    @7
    cN
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    @11
    dvdsmulf1o.y
    wph
    cN
    cn
    wcel
    @14
    @11
    wss
    dvdsmulf1o.2
    cN
    vx
    dvdsssfz1
    syl
    syl5eqss
    @11
    cY
    ssfi
    syl2anc
    #
    fsumdvdsmul.5
    fsumcl
    fsumdvdsmul.4
    fsummulc1
    wph
    cX
    @1
    @2
    vj
    wph
    vj
    cv
    #
    cX
    wcel
    #
    wa
    #
    @1
    cY
    cA
    cB
    cmul
    co
    #
    vk
    csu
    @2
    @18
    cY
    cB
    cA
    vk
    wph
    @12
    @17
    @15
    adantr
    fsumdvdsmul.4
    wph
    vk
    cv
    #
    cY
    wcel
    #
    cB
    cc
    wcel
    #
    @17
    fsumdvdsmul.5
    adantlr
    fsummulc2
    @18
    cY
    @19
    cD
    vk
    wph
    @17
    @21
    @19
    cD
    wceq
    fsumdvdsmul.6
    anassrs
    sumeq2dv
    eqtrd
    sumeq2dv
    wph
    @3
    cX
    cY
    cxp
    #
    vi
    vz
    cv
    #
    cmul
    cfv
    #
    cC
    csb
    #
    vz
    csu
    #
    @4
    wph
    vz
    cX
    cY
    cD
    @26
    vj
    vk
    @24
    @16
    @20
    cop
    #
    wceq
    #
    @26
    vi
    @16
    @20
    cmul
    co
    #
    cC
    csb
    cD
    @29
    vi
    @25
    @30
    cC
    @29
    @25
    @28
    cmul
    cfv
    @30
    @24
    @28
    cmul
    fveq2
    @16
    @20
    cmul
    df-ov
    syl6eqr
    csbeq1d
    vi
    @30
    cC
    cD
    @16
    @20
    cmul
    ovex
    fsumdvdsmul.7
    csbie
    syl6eq
    #
    @10
    @15
    wph
    @17
    @21
    wa
    wa
    #
    @19
    cD
    cc
    fsumdvdsmul.6
    @32
    cA
    cB
    wph
    @17
    cA
    cc
    wcel
    @21
    fsumdvdsmul.4
    adantrr
    wph
    @21
    @22
    @17
    fsumdvdsmul.5
    adantrl
    mulcld
    eqeltrrd
    #
    fsumxp
    wph
    @4
    cZ
    vi
    vw
    cv
    #
    cC
    csb
    #
    vw
    csu
    @27
    cZ
    cC
    @35
    vi
    vw
    vw
    cC
    nfcv
    vi
    @34
    cC
    nfcsb1v
    vi
    @34
    cC
    csbeq1a
    cbvsumi
    wph
    cZ
    @35
    @23
    @26
    vw
    vz
    cmul
    @23
    cres
    #
    @25
    vi
    @34
    @25
    cC
    csbeq1
    #
    wph
    @6
    @12
    @23
    cfn
    wcel
    @10
    @15
    cX
    cY
    xpfi
    syl2anc
    wph
    vx
    cM
    cN
    cX
    cY
    cZ
    dvdsmulf1o.1
    dvdsmulf1o.2
    dvdsmulf1o.3
    dvdsmulf1o.x
    dvdsmulf1o.y
    dvdsmulf1o.z
    dvdsmulf1o
    #
    @24
    @23
    wcel
    @24
    @36
    cfv
    @25
    wceq
    wph
    @24
    @23
    cmul
    fvres
    adantl
    wph
    @35
    cc
    wcel
    #
    vw
    cZ
    wph
    @26
    cc
    wcel
    #
    vz
    @23
    wral
    #
    @39
    vw
    cZ
    wral
    #
    wph
    cD
    cc
    wcel
    #
    vk
    cY
    wral
    vj
    cX
    wral
    @41
    wph
    @43
    vj
    vk
    cX
    cY
    @33
    ralrimivva
    @40
    @43
    vz
    vj
    vk
    cX
    cY
    @29
    @26
    cD
    cc
    @31
    eleq1d
    ralxp
    sylibr
    @41
    @39
    vw
    cmul
    @23
    cima
    #
    wral
    #
    wph
    @42
    cmul
    cc
    cc
    cxp
    #
    wfn
    #
    @23
    @46
    wss
    #
    @45
    @41
    wb
    @46
    cc
    cmul
    wf
    @47
    ax-mulf
    @46
    cc
    cmul
    ffn
    ax-mp
    cX
    cc
    wss
    cY
    cc
    wss
    @48
    cX
    cn
    cc
    cX
    @9
    cn
    dvdsmulf1o.x
    @8
    vx
    cn
    ssrab2
    eqsstri
    nnsscn
    sstri
    cY
    cn
    cc
    cY
    @14
    cn
    dvdsmulf1o.y
    @13
    vx
    cn
    ssrab2
    eqsstri
    nnsscn
    sstri
    cX
    cc
    cY
    cc
    xpss12
    mp2an
    @39
    @40
    vw
    vz
    @46
    @23
    cmul
    @34
    @25
    wceq
    @35
    @26
    cc
    @37
    eleq1d
    ralima
    mp2an
    wph
    @39
    vw
    @44
    cZ
    wph
    @44
    @36
    crn
    #
    cZ
    cmul
    @23
    df-ima
    wph
    @23
    cZ
    @36
    wf1o
    @23
    cZ
    @36
    wfo
    @49
    cZ
    wceq
    @38
    @23
    cZ
    @36
    f1ofo
    @23
    cZ
    @36
    forn
    3syl
    syl5eq
    raleqdv
    syl5bbr
    mpbid
    r19.21bi
    fsumf1o
    syl5eq
    eqtr4d
    3eqtrd
end
