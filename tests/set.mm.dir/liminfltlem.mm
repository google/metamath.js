include "cv.mm"
include "cfv.mm"
include "cneg.mm"
include "cmpt.mm"
include "cmin.mm"
include "co.mm"
include "clsp.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "clsi.mm"
include "caddc.mm"
include "nfmpt1.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "renegcld.mm"
include "fmptd2.mm"
include "cxr.mm"
include "cvv.mm"
include "fvexi.mm"
include "mptex.mm"
include "limsupcli.mm"
include "a1i.mm"
include "cxne.mm"
include "nfv.mm"
include "nfcv.mm"
include "liminfvaluz4.mm"
include "eqeltrrd.mm"
include "xnegrecl2d.mm"
include "limsupgt.mm"
include "wb.mm"
include "simpll.mm"
include "uztrn2.mm"
include "adantll.mm"
include "wceq.mm"
include "negex.mm"
include "fvmpt4.mm"
include "mpan2.mm"
include "adantl.mm"
include "oveq1d.mm"
include "recnd.mm"
include "rpred.mm"
include "adantr.mm"
include "negdi2d.mm"
include "eqtr4d.mm"
include "rexnegd.mm"
include "eqtr2d.mm"
include "negcon1ad.mm"
include "eqcomd.mm"
include "breq12d.mm"
include "readdcld.mm"
include "ltnegd.mm"
include "bitr4d.mm"
include "syl2anc.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "mpbid.mm"

theorem liminfltlem
  let wph: wff ph
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vx: setvar x
  assume liminfltlem.m: |- ( ph -> M e. ZZ )
  assume liminfltlem.z: |- Z = ( ZZ>= ` M )
  assume liminfltlem.f: |- ( ph -> F : Z --> RR )
  assume liminfltlem.r: |- ( ph -> ( liminf ` F ) e. RR )
  assume liminfltlem.x: |- ( ph -> X e. RR+ )

  disjoint F j
  disjoint F k
  disjoint j k
  disjoint M k
  disjoint X j
  disjoint X k
  disjoint Z j
  disjoint Z k
  disjoint j ph
  disjoint k ph
  disjoint k x
  assert |- ( ph -> E. j e. Z A. k e. ( ZZ>= ` j ) ( liminf ` F ) < ( ( F ` k ) + X ) )

  proof
    wph
    vk
    cv
    #
    vk
    cZ
    @0
    cF
    cfv
    #
    cneg
    #
    cmpt
    #
    cfv
    #
    cX
    cmin
    co
    #
    @3
    clsp
    cfv
    #
    clt
    wbr
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    cF
    clsi
    cfv
    #
    @1
    cX
    caddc
    co
    #
    clt
    wbr
    #
    vk
    @9
    wral
    #
    vj
    cZ
    wrex
    wph
    vj
    vk
    @3
    cM
    cX
    cZ
    vk
    cZ
    @2
    nfmpt1
    liminfltlem.m
    liminfltlem.z
    wph
    vk
    cZ
    @2
    cr
    wph
    @0
    cZ
    wcel
    #
    wa
    #
    @1
    wph
    cZ
    cr
    @0
    cF
    liminfltlem.f
    ffvelrnda
    #
    renegcld
    fmptd2
    wph
    @6
    @6
    cxr
    wcel
    wph
    @3
    cvv
    vk
    cZ
    @2
    cZ
    cM
    cuz
    liminfltlem.z
    fvexi
    mptex
    limsupcli
    a1i
    wph
    @11
    @6
    cxne
    #
    cr
    wph
    vk
    cF
    cM
    cZ
    wph
    vk
    nfv
    vk
    cF
    nfcv
    liminfltlem.m
    liminfltlem.z
    liminfltlem.f
    liminfvaluz4
    #
    liminfltlem.r
    eqeltrrd
    xnegrecl2d
    #
    liminfltlem.x
    limsupgt
    wph
    @10
    @14
    vj
    cZ
    wph
    @8
    cZ
    wcel
    #
    wa
    #
    @7
    @13
    vk
    @9
    @22
    @0
    @9
    wcel
    #
    wa
    wph
    @15
    @7
    @13
    wb
    wph
    @21
    @23
    simpll
    @21
    @23
    @15
    wph
    cM
    @0
    @8
    cZ
    liminfltlem.z
    uztrn2
    adantll
    @16
    @7
    @12
    cneg
    #
    @11
    cneg
    #
    clt
    wbr
    @13
    @16
    @5
    @24
    @6
    @25
    clt
    @16
    @5
    @2
    cX
    cmin
    co
    @24
    @16
    @4
    @2
    cX
    cmin
    @15
    @4
    @2
    wceq
    #
    wph
    @15
    @2
    cvv
    wcel
    @26
    @1
    negex
    vk
    cZ
    @2
    cvv
    fvmpt4
    mpan2
    adantl
    oveq1d
    @16
    @1
    cX
    @16
    @1
    @17
    recnd
    @16
    cX
    wph
    cX
    cr
    wcel
    @15
    wph
    cX
    liminfltlem.x
    rpred
    adantr
    #
    recnd
    negdi2d
    eqtr4d
    wph
    @6
    @25
    wceq
    @15
    wph
    @25
    @6
    wph
    @6
    @11
    wph
    @6
    @20
    recnd
    wph
    @11
    @18
    @6
    cneg
    @19
    wph
    @6
    @20
    rexnegd
    eqtr2d
    negcon1ad
    eqcomd
    adantr
    breq12d
    @16
    @11
    @12
    wph
    @11
    cr
    wcel
    @15
    liminfltlem.r
    adantr
    @16
    @1
    cX
    @17
    @27
    readdcld
    ltnegd
    bitr4d
    syl2anc
    ralbidva
    rexbidva
    mpbid
end
