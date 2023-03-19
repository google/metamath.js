include "clsxlim.mm"
include "wbr.mm"
include "cli.mm"
include "cmnf.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "cr.mm"
include "wa.mm"
include "cpnf.mm"
include "w3o.mm"
include "wcel.mm"
include "simplr.mm"
include "wb.mm"
include "cz.mm"
include "adantr.mm"
include "cxr.mm"
include "wf.mm"
include "simpr.mm"
include "xlimclim2.mm"
include "adantlr.mm"
include "mpbid.mm"
include "3mix1d.mm"
include "wn.mm"
include "simpl.mm"
include "breqtrd.mm"
include "adantll.mm"
include "nfcv.mm"
include "xlimmnf.mm"
include "ad2antrr.mm"
include "3mix2.mm"
include "syl2anc.mm"
include "simpll.mm"
include "xlimcl.mm"
include "ad3antlr.mm"
include "wne.mm"
include "neqne.mm"
include "adantl.mm"
include "xrnmnfpnf.mm"
include "xlimpnf.mm"
include "3mix3.mm"
include "pm2.61dan.mm"
include "climxlim2.mm"
include "biimpar.mm"
include "adantrl.mm"
include "simprl.mm"
include "breqtrrd.mm"
include "3jaodan.mm"
include "impbida.mm"

theorem dfxlim2v
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  assume dfxlim2v.1: |- ( ph -> M e. ZZ )
  assume dfxlim2v.2: |- Z = ( ZZ>= ` M )
  assume dfxlim2v.3: |- ( ph -> F : Z --> RR* )

  disjoint A j
  disjoint A k
  disjoint j k
  disjoint F j
  disjoint F k
  disjoint F x
  disjoint j x
  disjoint k x
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint j ph
  disjoint k ph
  disjoint k x
  assert |- ( ph -> ( F ~~>* A <-> ( F ~~> A \/ ( A = -oo /\ A. x e. RR E. j e. Z A. k e. ( ZZ>= ` j ) ( F ` k ) <_ x ) \/ ( A = +oo /\ A. x e. RR E. j e. Z A. k e. ( ZZ>= ` j ) x <_ ( F ` k ) ) ) ) )

  proof
    wph
    cF
    cA
    clsxlim
    wbr
    #
    cF
    cA
    cli
    wbr
    #
    cA
    cmnf
    wceq
    #
    vk
    cv
    cF
    cfv
    #
    vx
    cv
    #
    cle
    wbr
    vk
    vj
    cv
    cuz
    cfv
    #
    wral
    vj
    cZ
    wrex
    vx
    cr
    wral
    #
    wa
    #
    cA
    cpnf
    wceq
    #
    @4
    @3
    cle
    wbr
    vk
    @5
    wral
    vj
    cZ
    wrex
    vx
    cr
    wral
    #
    wa
    #
    w3o
    #
    wph
    @0
    wa
    #
    cA
    cr
    wcel
    #
    @11
    @12
    @13
    wa
    #
    @1
    @7
    @10
    @14
    @0
    @1
    wph
    @0
    @13
    simplr
    wph
    @13
    @0
    @1
    wb
    @0
    wph
    @13
    wa
    cA
    cF
    cM
    cZ
    wph
    cM
    cz
    wcel
    #
    @13
    dfxlim2v.1
    adantr
    dfxlim2v.2
    wph
    cZ
    cxr
    cF
    wf
    #
    @13
    dfxlim2v.3
    adantr
    wph
    @13
    simpr
    xlimclim2
    adantlr
    mpbid
    3mix1d
    @12
    @13
    wn
    #
    wa
    #
    @2
    @11
    @12
    @2
    @11
    @17
    @12
    @2
    wa
    #
    @2
    @6
    @11
    @12
    @2
    simpr
    @19
    cF
    cmnf
    clsxlim
    wbr
    #
    @6
    @0
    @2
    @20
    wph
    @0
    @2
    wa
    cF
    cA
    cmnf
    clsxlim
    @0
    @2
    simpl
    @0
    @2
    simpr
    breqtrd
    adantll
    wph
    @20
    @6
    wb
    @0
    @2
    wph
    vx
    vj
    vk
    cF
    cM
    cZ
    vk
    cF
    nfcv
    #
    dfxlim2v.1
    dfxlim2v.2
    dfxlim2v.3
    xlimmnf
    #
    ad2antrr
    mpbid
    @7
    @1
    @10
    3mix2
    syl2anc
    adantlr
    @18
    @2
    wn
    #
    wa
    #
    @12
    @8
    @11
    @12
    @17
    @23
    simpll
    @24
    cA
    @0
    cA
    cxr
    wcel
    wph
    @17
    @23
    cA
    cF
    xlimcl
    ad3antlr
    @12
    @17
    @23
    simplr
    @23
    cA
    cmnf
    wne
    @18
    cA
    cmnf
    neqne
    adantl
    xrnmnfpnf
    @12
    @8
    wa
    #
    @8
    @9
    @11
    @12
    @8
    simpr
    @25
    cF
    cpnf
    clsxlim
    wbr
    #
    @9
    @0
    @8
    @26
    wph
    @0
    @8
    wa
    cF
    cA
    cpnf
    clsxlim
    @0
    @8
    simpl
    @0
    @8
    simpr
    breqtrd
    adantll
    wph
    @26
    @9
    wb
    @0
    @8
    wph
    vx
    vj
    vk
    cF
    cM
    cZ
    @21
    dfxlim2v.1
    dfxlim2v.2
    dfxlim2v.3
    xlimpnf
    #
    ad2antrr
    mpbid
    @10
    @1
    @7
    3mix3
    syl2anc
    syl2anc
    pm2.61dan
    pm2.61dan
    wph
    @1
    @0
    @7
    @10
    wph
    @1
    wa
    cA
    cF
    cM
    cZ
    wph
    @15
    @1
    dfxlim2v.1
    adantr
    dfxlim2v.2
    wph
    @16
    @1
    dfxlim2v.3
    adantr
    wph
    @1
    simpr
    climxlim2
    wph
    @7
    wa
    cF
    cmnf
    cA
    clsxlim
    wph
    @6
    @20
    @2
    wph
    @20
    @6
    @22
    biimpar
    adantrl
    wph
    @2
    @6
    simprl
    breqtrrd
    wph
    @10
    wa
    cF
    cpnf
    cA
    clsxlim
    wph
    @9
    @26
    @8
    wph
    @26
    @9
    @27
    biimpar
    adantrl
    wph
    @8
    @9
    simprl
    breqtrrd
    3jaodan
    impbida
end
