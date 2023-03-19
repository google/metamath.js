include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "crn.mm"
include "wral.mm"
include "wex.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "crest.mm"
include "co.mm"
include "cn.mm"
include "cxp.mm"
include "cdom.mm"
include "com.mm"
include "cvv.mm"
include "wfn.mm"
include "cuz.mm"
include "fvex.mm"
include "eqeltri.mm"
include "nnex.mm"
include "xpex.mm"
include "a1i.mm"
include "c1.mm"
include "cdiv.mm"
include "caddc.mm"
include "clt.mm"
include "cdm.mm"
include "cin.mm"
include "wceq.mm"
include "wa.mm"
include "csalg.mm"
include "eqid.mm"
include "rabexd.mm"
include "adantr.mm"
include "ralrimivva.mm"
include "fnmpt2.mm"
include "syl.mm"
include "fnrndomg.mm"
include "sylc.mm"
include "uzct.mm"
include "nnct.mm"
include "pm3.2i.mm"
include "xpct.mm"
include "ax-mp.mm"
include "domtr.mm"
include "syl2anc.mm"
include "wrex.mm"
include "c0.mm"
include "wne.mm"
include "wb.mm"
include "vex.mm"
include "elrnmpt2g.mm"
include "biimpi.mm"
include "adantl.mm"
include "wi.mm"
include "w3a.mm"
include "simp3.mm"
include "csmblfn.mm"
include "ffvelrnda.mm"
include "adantrr.mm"
include "cr.mm"
include "nnrecre.mm"
include "readdcld.mm"
include "adantrl.mm"
include "smfpreimalt.mm"
include "dmex.mm"
include "elrest.mm"
include "mpbid.mm"
include "rabn0.mm"
include "sylibr.mm"
include "3adant3.mm"
include "eqnetrd.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "mpd.mm"
include "axccd2.mm"
include "cmpt2.mm"
include "ciin.mm"
include "ciun.mm"
include "cz.mm"
include "wf.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "cbvmpt2v.mm"
include "nfcv.mm"
include "nfmpt22.mm"
include "nfov.mm"
include "nfiin.mm"
include "nfiun.mm"
include "iineq2dv.mm"
include "cbviinv.mm"
include "eqtrd.mm"
include "iuneq2dv.mm"
include "cbviin.mm"
include "fveq2.mm"
include "id.mm"
include "eleq12d.mm"
include "rspccva.mm"
include "adantll.mm"
include "smflimlem5.mm"
include "ex.mm"
include "exlimdv.mm"

theorem smflimlem6
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cD: class D
  let cP: class P
  let cS: class S
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vs: setvar s
  let vc: setvar c
  let vr: setvar r
  let vi: setvar i
  let vj: setvar j
  let vl: setvar l
  let vy: setvar y
  assume smflimlem6.1: |- ( ph -> M e. ZZ )
  assume smflimlem6.2: |- Z = ( ZZ>= ` M )
  assume smflimlem6.3: |- ( ph -> S e. SAlg )
  assume smflimlem6.4: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smflimlem6.5: |- D = { x e. U_ n e. Z |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | ( m e. Z |-> ( ( F ` m ) ` x ) ) e. dom ~~> }
  assume smflimlem6.6: |- G = ( x e. D |-> ( ~~> ` ( m e. Z |-> ( ( F ` m ) ` x ) ) ) )
  assume smflimlem6.7: |- ( ph -> A e. RR )
  assume smflimlem6.8: |- P = ( m e. Z , k e. NN |-> { s e. S | { x e. dom ( F ` m ) | ( ( F ` m ) ` x ) < ( A + ( 1 / k ) ) } = ( s i^i dom ( F ` m ) ) } )

  disjoint A k
  disjoint A m
  disjoint A n
  disjoint A x
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint m n
  disjoint m x
  disjoint n x
  disjoint A s
  disjoint k s
  disjoint m s
  disjoint s x
  disjoint D k
  disjoint D m
  disjoint D n
  disjoint D x
  disjoint F k
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint F s
  disjoint G k
  disjoint G m
  disjoint G n
  disjoint M m
  disjoint P k
  disjoint P m
  disjoint P n
  disjoint P x
  disjoint P s
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S s
  disjoint Z k
  disjoint Z m
  disjoint Z n
  disjoint Z x
  disjoint Z s
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint k x
  disjoint A c
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c x
  disjoint c s
  disjoint D c
  disjoint D r
  disjoint c r
  disjoint k r
  disjoint m r
  disjoint n r
  disjoint r x
  disjoint G c
  disjoint P c
  disjoint P i
  disjoint P j
  disjoint P l
  disjoint P r
  disjoint c i
  disjoint c j
  disjoint c l
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint i n
  disjoint i r
  disjoint i x
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint j n
  disjoint j r
  disjoint j x
  disjoint k l
  disjoint l m
  disjoint l n
  disjoint l r
  disjoint l x
  disjoint j s
  disjoint l s
  disjoint P y
  disjoint c y
  disjoint k y
  disjoint m y
  disjoint n y
  disjoint r y
  disjoint x y
  disjoint S c
  disjoint Z i
  disjoint Z j
  disjoint Z l
  disjoint Z r
  disjoint c ph
  disjoint ph r
  disjoint ph y
  assert |- ( ph -> { x e. D | ( G ` x ) <_ A } e. ( S |`t D ) )

  proof
    wph
    vy
    cv
    #
    vc
    cv
    #
    cfv
    #
    @0
    wcel
    #
    vy
    cP
    crn
    #
    wral
    #
    vc
    wex
    vx
    cv
    #
    cG
    cfv
    cA
    cle
    wbr
    vx
    cD
    crab
    cS
    cD
    crest
    co
    wcel
    #
    wph
    vy
    @4
    vc
    wph
    @4
    cZ
    cn
    cxp
    #
    cdom
    wbr
    #
    @8
    com
    cdom
    wbr
    #
    @4
    com
    cdom
    wbr
    wph
    @8
    cvv
    wcel
    #
    cP
    @8
    wfn
    #
    @9
    @11
    wph
    cZ
    cn
    cZ
    cM
    cuz
    cfv
    cvv
    smflimlem6.2
    cM
    cuz
    fvex
    eqeltri
    nnex
    xpex
    a1i
    wph
    @6
    vm
    cv
    #
    cF
    cfv
    #
    cfv
    cA
    c1
    vk
    cv
    #
    cdiv
    co
    #
    caddc
    co
    #
    clt
    wbr
    vx
    @14
    cdm
    #
    crab
    #
    vs
    cv
    @18
    cin
    wceq
    #
    vs
    cS
    crab
    #
    cvv
    wcel
    #
    vk
    cn
    wral
    vm
    cZ
    wral
    @12
    wph
    @22
    vm
    vk
    cZ
    cn
    wph
    @22
    @13
    cZ
    wcel
    #
    @15
    cn
    wcel
    #
    wa
    #
    wph
    @20
    vs
    cS
    @21
    csalg
    @21
    eqid
    smflimlem6.3
    rabexd
    adantr
    ralrimivva
    vm
    vk
    cZ
    cn
    @21
    cP
    cvv
    smflimlem6.8
    fnmpt2
    syl
    @8
    cvv
    cP
    fnrndomg
    sylc
    @10
    wph
    cZ
    com
    cdom
    wbr
    #
    cn
    com
    cdom
    wbr
    #
    wa
    @10
    @26
    @27
    cM
    cZ
    smflimlem6.2
    uzct
    nnct
    pm3.2i
    cZ
    cn
    xpct
    ax-mp
    a1i
    @4
    @8
    com
    domtr
    syl2anc
    wph
    @0
    @4
    wcel
    #
    wa
    @0
    @21
    wceq
    #
    vk
    cn
    wrex
    vm
    cZ
    wrex
    #
    @0
    c0
    wne
    #
    @28
    @30
    wph
    @28
    @30
    @0
    cvv
    wcel
    @28
    @30
    wb
    vy
    vex
    vm
    vk
    cZ
    cn
    @21
    @0
    cP
    cvv
    smflimlem6.8
    elrnmpt2g
    ax-mp
    biimpi
    adantl
    wph
    @30
    @31
    wi
    @28
    wph
    @29
    @31
    vm
    vk
    cZ
    cn
    wph
    @25
    @29
    @31
    wph
    @25
    @29
    w3a
    @0
    @21
    c0
    wph
    @25
    @29
    simp3
    wph
    @25
    @21
    c0
    wne
    #
    @29
    wph
    @25
    wa
    #
    @20
    vs
    cS
    wrex
    #
    @32
    @33
    @19
    cS
    @18
    crest
    co
    wcel
    #
    @34
    @33
    vx
    @17
    @18
    cS
    @14
    wph
    cS
    csalg
    wcel
    #
    @25
    smflimlem6.3
    adantr
    wph
    @23
    @14
    cS
    csmblfn
    cfv
    #
    wcel
    @24
    wph
    cZ
    @37
    @13
    cF
    smflimlem6.4
    ffvelrnda
    adantrr
    @18
    eqid
    wph
    @24
    @17
    cr
    wcel
    @23
    wph
    @24
    wa
    cA
    @16
    wph
    cA
    cr
    wcel
    #
    @24
    smflimlem6.7
    adantr
    @24
    @16
    cr
    wcel
    wph
    @15
    nnrecre
    adantl
    readdcld
    adantrl
    smfpreimalt
    wph
    @35
    @34
    wb
    #
    @25
    wph
    @36
    @18
    cvv
    wcel
    #
    @39
    smflimlem6.3
    @40
    wph
    @14
    @13
    cF
    fvex
    dmex
    a1i
    vs
    @19
    @18
    cS
    csalg
    cvv
    elrest
    syl2anc
    adantr
    mpbid
    @20
    vs
    cS
    rabn0
    sylibr
    3adant3
    eqnetrd
    3exp
    rexlimdvv
    adantr
    mpd
    axccd2
    wph
    @5
    @7
    vc
    wph
    @5
    @7
    wph
    @5
    wa
    vx
    cA
    @1
    cD
    cP
    cS
    vk
    vm
    vn
    cF
    cG
    vl
    vj
    cZ
    cn
    vl
    cv
    #
    vj
    cv
    #
    cP
    co
    #
    @1
    cfv
    #
    cmpt2
    #
    vj
    cn
    vn
    cZ
    vi
    vn
    cv
    #
    cuz
    cfv
    #
    vi
    cv
    #
    @42
    @45
    co
    #
    ciin
    #
    ciun
    #
    ciin
    cM
    cZ
    vs
    vr
    wph
    cM
    cz
    wcel
    @5
    smflimlem6.1
    adantr
    smflimlem6.2
    wph
    @36
    @5
    smflimlem6.3
    adantr
    wph
    cZ
    @37
    cF
    wf
    @5
    smflimlem6.4
    adantr
    smflimlem6.5
    smflimlem6.6
    wph
    @38
    @5
    smflimlem6.7
    adantr
    smflimlem6.8
    vl
    vj
    vm
    vk
    cZ
    cn
    @44
    @13
    @15
    cP
    co
    #
    @1
    cfv
    @13
    @42
    cP
    co
    #
    @1
    cfv
    @41
    @13
    wceq
    @43
    @53
    @1
    @41
    @13
    @42
    cP
    oveq1
    fveq2d
    @42
    @15
    wceq
    #
    @53
    @52
    @1
    @42
    @15
    @13
    cP
    oveq2
    fveq2d
    cbvmpt2v
    vj
    vk
    cn
    @51
    vn
    cZ
    vm
    @47
    @13
    @15
    @45
    co
    #
    ciin
    #
    ciun
    vk
    @51
    nfcv
    vn
    vj
    cZ
    @56
    vj
    cZ
    nfcv
    vm
    vj
    @47
    @55
    vj
    @47
    nfcv
    vj
    @13
    @15
    @45
    vj
    @13
    nfcv
    vl
    vj
    cZ
    cn
    @44
    nfmpt22
    vj
    @15
    nfcv
    nfov
    nfiin
    nfiun
    @54
    vn
    cZ
    @50
    @56
    @54
    @50
    @56
    wceq
    @46
    cZ
    wcel
    @54
    @50
    vi
    @47
    @48
    @15
    @45
    co
    #
    ciin
    #
    @56
    @54
    vi
    @47
    @49
    @57
    @54
    @49
    @57
    wceq
    @48
    @47
    wcel
    @42
    @15
    @48
    @45
    oveq2
    adantr
    iineq2dv
    @58
    @56
    wceq
    @54
    vi
    vm
    @47
    @57
    @55
    @48
    @13
    @15
    @45
    oveq1
    cbviinv
    a1i
    eqtrd
    adantr
    iuneq2dv
    cbviin
    @5
    vr
    cv
    #
    @4
    wcel
    @59
    @1
    cfv
    #
    @59
    wcel
    #
    wph
    @3
    @61
    vy
    @59
    @4
    @0
    @59
    wceq
    #
    @2
    @60
    @0
    @59
    @0
    @59
    @1
    fveq2
    @62
    id
    eleq12d
    rspccva
    adantll
    smflimlem5
    ex
    exlimdv
    mpd
end
