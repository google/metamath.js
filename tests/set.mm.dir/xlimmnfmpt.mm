include "cmnf.mm"
include "clsxlim.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "cr.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "cxr.mm"
include "fmptdf.mm"
include "xlimmnf.mm"
include "wcel.mm"
include "wa.mm"
include "nfv.mm"
include "nfan.mm"
include "wceq.mm"
include "uztrn2.mm"
include "adantll.mm"
include "simpll.mm"
include "syl2anc.mm"
include "fvmpt2.mm"
include "breq1d.mm"
include "ralbida.mm"
include "rexbidva.mm"
include "ralbidv.mm"
include "wb.mm"
include "weq.mm"
include "breq2.mm"
include "rexralbidv.mm"
include "fveq2.mm"
include "raleqdv.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "cbvralv.mm"
include "a1i.mm"
include "3bitrd.mm"

theorem xlimmnfmpt
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vi: setvar i
  let vy: setvar y
  assume xlimmnfmpt.k: |- F/ k ph
  assume xlimmnfmpt.m: |- ( ph -> M e. ZZ )
  assume xlimmnfmpt.z: |- Z = ( ZZ>= ` M )
  assume xlimmnfmpt.b: |- ( ( ph /\ k e. Z ) -> B e. RR* )
  assume xlimmnfmpt.f: |- F = ( k e. Z |-> B )

  disjoint B j
  disjoint B x
  disjoint j x
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint j k
  disjoint k x
  disjoint k x
  disjoint B i
  disjoint B y
  disjoint i j
  disjoint i x
  disjoint i y
  disjoint j y
  disjoint x y
  disjoint F i
  disjoint F y
  disjoint Z i
  disjoint Z y
  disjoint i k
  disjoint k y
  disjoint i ph
  disjoint ph y
  assert |- ( ph -> ( F ~~>* -oo <-> A. x e. RR E. j e. Z A. k e. ( ZZ>= ` j ) B <_ x ) )

  proof
    wph
    cF
    cmnf
    clsxlim
    wbr
    vk
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vk
    vi
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vi
    cZ
    wrex
    #
    vy
    cr
    wral
    cB
    @2
    cle
    wbr
    #
    vk
    @5
    wral
    #
    vi
    cZ
    wrex
    #
    vy
    cr
    wral
    #
    cB
    vx
    cv
    #
    cle
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
    #
    vx
    cr
    wral
    #
    wph
    vy
    vi
    vk
    cF
    cM
    cZ
    vk
    cF
    vk
    cZ
    cB
    cmpt
    xlimmnfmpt.f
    vk
    cZ
    cB
    nfmpt1
    nfcxfr
    xlimmnfmpt.m
    xlimmnfmpt.z
    wph
    vk
    cZ
    cB
    cxr
    cF
    xlimmnfmpt.k
    xlimmnfmpt.b
    xlimmnfmpt.f
    fmptdf
    xlimmnf
    wph
    @7
    @10
    vy
    cr
    wph
    @6
    @9
    vi
    cZ
    wph
    @4
    cZ
    wcel
    #
    wa
    #
    @3
    @8
    vk
    @5
    wph
    @19
    vk
    xlimmnfmpt.k
    @19
    vk
    nfv
    nfan
    @20
    @0
    @5
    wcel
    #
    wa
    #
    @1
    cB
    @2
    cle
    @22
    @0
    cZ
    wcel
    #
    cB
    cxr
    wcel
    #
    @1
    cB
    wceq
    @19
    @21
    @23
    wph
    cM
    @0
    @4
    cZ
    xlimmnfmpt.z
    uztrn2
    adantll
    #
    @22
    wph
    @23
    @24
    wph
    @19
    @21
    simpll
    @25
    xlimmnfmpt.b
    syl2anc
    vk
    cZ
    cB
    cxr
    cF
    xlimmnfmpt.f
    fvmpt2
    syl2anc
    breq1d
    ralbida
    rexbidva
    ralbidv
    @11
    @18
    wb
    wph
    @10
    @17
    vy
    vx
    cr
    vy
    vx
    weq
    #
    @10
    @13
    vk
    @5
    wral
    #
    vi
    cZ
    wrex
    @17
    @26
    @8
    @13
    vi
    vk
    cZ
    @5
    @2
    @12
    cB
    cle
    breq2
    rexralbidv
    @27
    @16
    vi
    vj
    cZ
    vi
    vj
    weq
    @13
    vk
    @5
    @15
    @4
    @14
    cuz
    fveq2
    raleqdv
    cbvrexv
    syl6bb
    cbvralv
    a1i
    3bitrd
end
