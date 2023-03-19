include "csupp.mm"
include "co.mm"
include "cdm.mm"
include "cres.mm"
include "cgsu.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cmpt.mm"
include "gsum2dlem2.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "suppssdm.mm"
include "wf.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "wrel.mm"
include "wss.mm"
include "relss.mm"
include "sylc.mm"
include "crn.mm"
include "relssdmrn.mm"
include "ssv.mm"
include "xpss2.mm"
include "ax-mp.mm"
include "syl6ss.mm"
include "ssind.mm"
include "df-res.mm"
include "syl6sseqr.mm"
include "gsumres.mm"
include "dmss.mm"
include "sstrd.mm"
include "resmptd.mm"
include "oveq2d.mm"
include "wcel.mm"
include "gsum2dlem1.mm"
include "adantr.mm"
include "eqid.mm"
include "fmptd.mm"
include "cdif.mm"
include "wa.mm"
include "cop.mm"
include "vex.mm"
include "elimasn.mm"
include "biimpi.mm"
include "ad2antll.mm"
include "wn.mm"
include "eldifn.mm"
include "ad2antrl.mm"
include "opeldm.mm"
include "nsyl.mm"
include "eldifd.mm"
include "cfv.mm"
include "df-ov.mm"
include "ssid.mm"
include "a1i.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "suppssr.mm"
include "syl5eq.mm"
include "syldan.mm"
include "anassrs.mm"
include "mpteq2dva.mm"
include "cmnd.mm"
include "ccmn.mm"
include "cmnmnd.mm"
include "imaexg.mm"
include "gsumz.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "suppss2.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wfun.mm"
include "cfn.mm"
include "funmpt.mm"
include "fsuppimpd.mm"
include "dmfi.mm"
include "ssfi.mm"
include "wb.mm"
include "mptexg.mm"
include "isfsupp.mm"
include "mpbir2and.mm"
include "eqtr3d.mm"
include "3eqtr3d.mm"

theorem gsum2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume gsum2d.b: |- B = ( Base ` G )
  assume gsum2d.z: |- .0. = ( 0g ` G )
  assume gsum2d.g: |- ( ph -> G e. CMnd )
  assume gsum2d.a: |- ( ph -> A e. V )
  assume gsum2d.r: |- ( ph -> Rel A )
  assume gsum2d.d: |- ( ph -> D e. W )
  assume gsum2d.s: |- ( ph -> dom A C_ D )
  assume gsum2d.f: |- ( ph -> F : A --> B )
  assume gsum2d.w: |- ( ph -> F finSupp .0. )

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint F j
  disjoint F k
  disjoint G j
  disjoint G k
  disjoint j ph
  disjoint k ph
  disjoint B j
  disjoint B k
  disjoint D j
  disjoint D k
  disjoint .0. j
  disjoint .0. k
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint .0. x
  disjoint .0. y
  disjoint .0. z
  assert |- ( ph -> ( G gsum F ) = ( G gsum ( j e. D |-> ( G gsum ( k e. ( A " { j } ) |-> ( j F k ) ) ) ) ) )

  proof
    wph
    cG
    cF
    cA
    cF
    c.0
    csupp
    co
    #
    cdm
    #
    cres
    #
    cres
    cgsu
    co
    cG
    vj
    @1
    cG
    vk
    cA
    vj
    cv
    #
    csn
    #
    cima
    #
    @3
    vk
    cv
    #
    cF
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cG
    cF
    cgsu
    co
    cG
    vj
    cD
    @9
    cmpt
    #
    cgsu
    co
    #
    wph
    cA
    cB
    cD
    vj
    vk
    cF
    cG
    cV
    cW
    c.0
    gsum2d.b
    gsum2d.z
    gsum2d.g
    gsum2d.a
    gsum2d.r
    gsum2d.d
    gsum2d.s
    gsum2d.f
    gsum2d.w
    gsum2dlem2
    wph
    cA
    cB
    cF
    cG
    cV
    @2
    c.0
    gsum2d.b
    gsum2d.z
    gsum2d.g
    gsum2d.a
    gsum2d.f
    wph
    @0
    cA
    @1
    cvv
    cxp
    #
    cin
    @2
    wph
    @0
    cA
    @14
    wph
    cF
    cdm
    #
    @0
    cA
    cF
    c.0
    suppssdm
    wph
    cA
    cB
    cF
    wf
    @15
    cA
    wceq
    gsum2d.f
    cA
    cB
    cF
    fdm
    syl
    syl5sseq
    #
    wph
    @0
    wrel
    #
    @0
    @14
    wss
    wph
    @0
    cA
    wss
    #
    cA
    wrel
    @17
    @16
    gsum2d.r
    @0
    cA
    relss
    sylc
    @17
    @0
    @1
    @0
    crn
    #
    cxp
    #
    @14
    @0
    relssdmrn
    @19
    cvv
    wss
    @20
    @14
    wss
    @19
    ssv
    @19
    cvv
    @1
    xpss2
    ax-mp
    syl6ss
    syl
    ssind
    cA
    @1
    df-res
    syl6sseqr
    gsum2d.w
    gsumres
    wph
    cG
    @12
    @1
    cres
    #
    cgsu
    co
    @11
    @13
    wph
    @21
    @10
    cG
    cgsu
    wph
    vj
    cD
    @1
    @9
    wph
    @1
    cA
    cdm
    #
    cD
    wph
    @18
    @1
    @22
    wss
    @16
    @0
    cA
    dmss
    syl
    gsum2d.s
    sstrd
    resmptd
    oveq2d
    wph
    cD
    cB
    @12
    cG
    cW
    @1
    c.0
    gsum2d.b
    gsum2d.z
    gsum2d.g
    gsum2d.d
    wph
    vj
    cD
    @9
    cB
    @12
    wph
    @9
    cB
    wcel
    @3
    cD
    wcel
    wph
    cA
    cB
    cD
    vj
    vk
    cF
    cG
    cV
    cW
    c.0
    gsum2d.b
    gsum2d.z
    gsum2d.g
    gsum2d.a
    gsum2d.r
    gsum2d.d
    gsum2d.s
    gsum2d.f
    gsum2d.w
    gsum2dlem1
    adantr
    @12
    eqid
    fmptd
    wph
    cD
    @9
    vj
    cW
    @1
    c.0
    wph
    @3
    cD
    @1
    cdif
    wcel
    #
    wa
    #
    @9
    cG
    vk
    @5
    c.0
    cmpt
    #
    cgsu
    co
    #
    c.0
    @24
    @8
    @25
    cG
    cgsu
    @24
    vk
    @5
    @7
    c.0
    wph
    @23
    @6
    @5
    wcel
    #
    @7
    c.0
    wceq
    #
    wph
    @23
    @27
    wa
    #
    @3
    @6
    cop
    #
    cA
    @0
    cdif
    wcel
    #
    @28
    wph
    @29
    wa
    #
    @30
    cA
    @0
    @27
    @30
    cA
    wcel
    #
    wph
    @23
    @27
    @33
    cA
    @3
    @6
    vj
    vex
    #
    vk
    vex
    #
    elimasn
    biimpi
    ad2antll
    @32
    @3
    @1
    wcel
    #
    @30
    @0
    wcel
    @23
    @36
    wn
    wph
    @27
    @3
    cD
    @1
    eldifn
    ad2antrl
    @3
    @6
    @0
    @34
    @35
    opeldm
    nsyl
    eldifd
    wph
    @31
    wa
    @7
    @30
    cF
    cfv
    c.0
    @3
    @6
    cF
    df-ov
    wph
    cA
    cB
    cvv
    cF
    cV
    @0
    @30
    c.0
    gsum2d.f
    @0
    @0
    wss
    wph
    @0
    ssid
    a1i
    gsum2d.a
    c.0
    cvv
    wcel
    #
    wph
    c.0
    cG
    c0g
    cfv
    cvv
    gsum2d.z
    cG
    c0g
    fvex
    eqeltri
    a1i
    #
    suppssr
    syl5eq
    syldan
    anassrs
    mpteq2dva
    oveq2d
    wph
    @26
    c.0
    wceq
    #
    @23
    wph
    cG
    cmnd
    wcel
    #
    @5
    cvv
    wcel
    #
    @39
    wph
    cG
    ccmn
    wcel
    @40
    gsum2d.g
    cG
    cmnmnd
    syl
    wph
    cA
    cV
    wcel
    @41
    gsum2d.a
    cA
    @4
    cV
    imaexg
    syl
    @5
    vk
    cG
    cvv
    c.0
    gsum2d.z
    gsumz
    syl2anc
    adantr
    eqtrd
    gsum2d.d
    suppss2
    #
    wph
    @12
    c.0
    cfsupp
    wbr
    #
    @12
    wfun
    #
    @12
    c.0
    csupp
    co
    #
    cfn
    wcel
    #
    @44
    wph
    vj
    cD
    @9
    funmpt
    a1i
    wph
    @1
    cfn
    wcel
    #
    @45
    @1
    wss
    @46
    wph
    @0
    cfn
    wcel
    @47
    wph
    cF
    c.0
    gsum2d.w
    fsuppimpd
    @0
    dmfi
    syl
    @42
    @1
    @45
    ssfi
    syl2anc
    wph
    @12
    cvv
    wcel
    #
    @37
    @43
    @44
    @46
    wa
    wb
    wph
    cD
    cW
    wcel
    @48
    gsum2d.d
    vj
    cD
    @9
    cW
    mptexg
    syl
    @38
    @12
    cvv
    cvv
    c.0
    isfsupp
    syl2anc
    mpbir2and
    gsumres
    eqtr3d
    3eqtr3d
end
