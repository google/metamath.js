include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cdm.mm"
include "ciin.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "csmblfn.mm"
include "cxr.mm"
include "wceq.mm"
include "a1i.mm"
include "wcel.mm"
include "wa.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfii1.mm"
include "nfel.mm"
include "nfan.mm"
include "c0.mm"
include "wne.mm"
include "uzn0d.mm"
include "adantr.mm"
include "wf.mm"
include "csalg.mm"
include "ffvelrnda.mm"
include "eqid.mm"
include "smff.mm"
include "adantlr.mm"
include "eliinid.mm"
include "adantll.mm"
include "ffvelrnd.mm"
include "supxrre3rnmpt.mm"
include "rabbidva.mm"
include "eqtrd.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfsup.mm"
include "nfrab.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfdm.mm"
include "nfiin.mm"
include "ssrab2f.mm"
include "eqsstri.mm"
include "id.mm"
include "sseldi.mm"
include "sylan.mm"
include "syl6eleq.mm"
include "rabidim2.mm"
include "syl.mm"
include "adantl.mm"
include "wb.mm"
include "syldan.mm"
include "mpbid.mm"
include "supxrrernmpt.mm"
include "mpteq12dva.mm"
include "smfsup.mm"
include "eqeltrd.mm"

theorem smfsupxr
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vy: setvar y
  let vk: setvar k
  assume smfsupxr.n: |- F/_ n F
  assume smfsupxr.x: |- F/_ x F
  assume smfsupxr.m: |- ( ph -> M e. ZZ )
  assume smfsupxr.z: |- Z = ( ZZ>= ` M )
  assume smfsupxr.s: |- ( ph -> S e. SAlg )
  assume smfsupxr.f: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smfsupxr.d: |- D = { x e. |^|_ n e. Z dom ( F ` n ) | sup ( ran ( n e. Z |-> ( ( F ` n ) ` x ) ) , RR* , < ) e. RR }
  assume smfsupxr.g: |- G = ( x e. D |-> sup ( ran ( n e. Z |-> ( ( F ` n ) ` x ) ) , RR* , < ) )

  disjoint Z n
  disjoint Z x
  disjoint n x
  disjoint n ph
  disjoint ph x
  disjoint F y
  disjoint Z y
  disjoint n y
  disjoint x y
  disjoint k x
  assert |- ( ph -> G e. ( SMblFn ` S ) )

  proof
    wph
    cG
    vx
    vx
    cv
    #
    vn
    cv
    #
    cF
    cfv
    #
    cfv
    #
    vy
    cv
    cle
    wbr
    vn
    cZ
    wral
    vy
    cr
    wrex
    #
    vx
    vn
    cZ
    @2
    cdm
    #
    ciin
    #
    crab
    #
    vn
    cZ
    @3
    cmpt
    #
    crn
    #
    cr
    clt
    csup
    #
    cmpt
    #
    cS
    csmblfn
    cfv
    #
    wph
    cG
    vx
    cD
    @9
    cxr
    clt
    csup
    #
    cmpt
    #
    @11
    cG
    @14
    wceq
    wph
    smfsupxr.g
    a1i
    wph
    vx
    cD
    @13
    @7
    @10
    wph
    cD
    @13
    cr
    wcel
    #
    vx
    @6
    crab
    #
    @7
    cD
    @16
    wceq
    wph
    smfsupxr.d
    a1i
    wph
    @15
    @4
    vx
    @6
    wph
    @0
    @6
    wcel
    #
    wa
    #
    vn
    vy
    cZ
    @3
    wph
    @17
    vn
    wph
    vn
    nfv
    #
    vn
    @0
    @6
    vn
    @0
    nfcv
    #
    vn
    cZ
    @5
    nfii1
    #
    nfel
    nfan
    wph
    cZ
    c0
    wne
    #
    @17
    wph
    cM
    cZ
    smfsupxr.m
    smfsupxr.z
    uzn0d
    #
    adantr
    @18
    @1
    cZ
    wcel
    #
    wa
    @5
    cr
    @0
    @2
    wph
    @24
    @5
    cr
    @2
    wf
    #
    @17
    wph
    @24
    wa
    @5
    cS
    @2
    wph
    cS
    csalg
    wcel
    @24
    smfsupxr.s
    adantr
    wph
    cZ
    @12
    @1
    cF
    smfsupxr.f
    ffvelrnda
    @5
    eqid
    smff
    #
    adantlr
    @17
    @24
    @0
    @5
    wcel
    #
    wph
    vn
    @0
    cZ
    @5
    eliinid
    #
    adantll
    ffvelrnd
    supxrre3rnmpt
    #
    rabbidva
    eqtrd
    wph
    @0
    cD
    wcel
    #
    wa
    #
    vn
    vy
    cZ
    @3
    wph
    @30
    vn
    @19
    vn
    @0
    cD
    @20
    vn
    cD
    @16
    smfsupxr.d
    @15
    vn
    vx
    @6
    vn
    @13
    cr
    vn
    @9
    cxr
    clt
    vn
    @8
    vn
    cZ
    @3
    nfmpt1
    nfrn
    vn
    cxr
    nfcv
    vn
    clt
    nfcv
    nfsup
    vn
    cr
    nfcv
    nfel
    @21
    nfrab
    nfcxfr
    nfel
    nfan
    wph
    @22
    @30
    @23
    adantr
    @31
    @24
    wa
    @5
    cr
    @0
    @2
    wph
    @24
    @25
    @30
    @26
    adantlr
    @30
    @24
    @27
    wph
    @30
    @17
    @24
    @27
    @30
    cD
    @6
    @0
    cD
    @16
    @6
    smfsupxr.d
    @15
    vx
    @6
    vn
    vx
    cZ
    @5
    vx
    cZ
    nfcv
    vx
    @2
    vx
    @1
    cF
    smfsupxr.x
    vx
    @1
    nfcv
    nffv
    nfdm
    nfiin
    ssrab2f
    eqsstri
    @30
    id
    #
    sseldi
    #
    @28
    sylan
    adantll
    ffvelrnd
    @31
    @15
    @4
    @30
    @15
    wph
    @30
    @0
    @16
    wcel
    @15
    @30
    @0
    cD
    @16
    @32
    smfsupxr.d
    syl6eleq
    @15
    vx
    @6
    rabidim2
    syl
    adantl
    wph
    @30
    @17
    @15
    @4
    wb
    @30
    @17
    wph
    @33
    adantl
    @29
    syldan
    mpbid
    supxrrernmpt
    mpteq12dva
    eqtrd
    wph
    vx
    vy
    @7
    cS
    vn
    cF
    @11
    cM
    cZ
    smfsupxr.n
    smfsupxr.x
    smfsupxr.m
    smfsupxr.z
    smfsupxr.s
    smfsupxr.f
    @7
    eqid
    @11
    eqid
    smfsup
    eqeltrd
end
