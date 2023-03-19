include "cv.mm"
include "cdm.mm"
include "wcel.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cuz.mm"
include "cfv.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "cc.mm"
include "cpm.mm"
include "wa.mm"
include "cca.mm"
include "cxmt.mm"
include "cvv.mm"
include "wf.mm"
include "wss.mm"
include "elfvdm.mm"
include "syl.mm"
include "cnex.mm"
include "jctir.mm"
include "cz.mm"
include "uzssz.mm"
include "zsscn.mm"
include "sstri.mm"
include "eqsstri.mm"
include "elpm2r.mm"
include "syl2anc.mm"
include "biantrurd.mm"
include "wb.mm"
include "wceq.mm"
include "adantr.mm"
include "adantrr.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "eqeltrrd.mm"
include "uztrn2.mm"
include "sylan2.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "xmetsym.mm"
include "syl3anc.mm"
include "breq1d.mm"
include "fdm.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "jca.mm"
include "df-3an.mm"
include "syl6bbr.mm"
include "bitrd.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "ralbidv.mm"
include "iscau4.mm"
include "3bitr4rd.mm"

theorem iscauf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vd: setvar d
  let vf: setvar f
  let vm: setvar m
  assume iscau3.2: |- Z = ( ZZ>= ` M )
  assume iscau3.3: |- ( ph -> D e. ( *Met ` X ) )
  assume iscau3.4: |- ( ph -> M e. ZZ )
  assume iscau4.5: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )
  assume iscau4.6: |- ( ( ph /\ j e. Z ) -> ( F ` j ) = B )
  assume iscauf.7: |- ( ph -> F : Z --> X )

  disjoint j k
  disjoint j x
  disjoint D j
  disjoint k x
  disjoint D k
  disjoint D x
  disjoint F j
  disjoint F k
  disjoint F x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint X j
  disjoint X k
  disjoint X x
  disjoint M j
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint d f
  disjoint d j
  disjoint d k
  disjoint d m
  disjoint d x
  disjoint D d
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f x
  disjoint D f
  disjoint j m
  disjoint k m
  disjoint m x
  disjoint D m
  disjoint F f
  disjoint F m
  disjoint X d
  disjoint X f
  disjoint X m
  disjoint Z m
  assert |- ( ph -> ( F e. ( Cau ` D ) <-> A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( B D A ) < x ) )

  proof
    wph
    vk
    cv
    #
    cF
    cdm
    #
    wcel
    #
    cA
    cX
    wcel
    #
    cA
    cB
    cD
    co
    #
    vx
    cv
    #
    clt
    wbr
    #
    w3a
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
    crp
    wral
    #
    cF
    cX
    cc
    cpm
    co
    wcel
    #
    @12
    wa
    cB
    cA
    cD
    co
    #
    @5
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
    #
    vx
    crp
    wral
    cF
    cD
    cca
    cfv
    wcel
    wph
    @13
    @12
    wph
    cX
    cxmt
    cdm
    #
    wcel
    #
    cc
    cvv
    wcel
    #
    wa
    cZ
    cX
    cF
    wf
    #
    cZ
    cc
    wss
    #
    wa
    @13
    wph
    @19
    @20
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @19
    iscau3.3
    cD
    cX
    cxmt
    elfvdm
    syl
    cnex
    jctir
    wph
    @21
    @22
    iscauf.7
    cZ
    cM
    cuz
    cfv
    #
    cc
    iscau3.2
    @24
    cz
    cc
    cM
    uzssz
    zsscn
    sstri
    eqsstri
    jctir
    cX
    cc
    cZ
    cF
    @18
    cvv
    elpm2r
    syl2anc
    biantrurd
    wph
    @17
    @11
    vx
    crp
    wph
    @16
    @10
    vj
    cZ
    wph
    @8
    cZ
    wcel
    #
    wa
    @15
    @7
    vk
    @9
    wph
    @25
    @0
    @9
    wcel
    #
    @15
    @7
    wb
    wph
    @25
    @26
    wa
    #
    wa
    #
    @15
    @6
    @7
    @28
    @14
    @4
    @5
    clt
    @28
    @23
    cB
    cX
    wcel
    @3
    @14
    @4
    wceq
    wph
    @23
    @27
    iscau3.3
    adantr
    @28
    @8
    cF
    cfv
    #
    cB
    cX
    wph
    @25
    @29
    cB
    wceq
    @26
    iscau4.6
    adantrr
    @28
    cZ
    cX
    @8
    cF
    wph
    @21
    @27
    iscauf.7
    adantr
    wph
    @25
    @26
    simprl
    ffvelrnd
    eqeltrrd
    @28
    @0
    cF
    cfv
    #
    cA
    cX
    @27
    wph
    @0
    cZ
    wcel
    #
    @30
    cA
    wceq
    cM
    @0
    @8
    cZ
    iscau3.2
    uztrn2
    #
    iscau4.5
    sylan2
    wph
    @21
    @31
    @30
    cX
    wcel
    @27
    iscauf.7
    @32
    cZ
    cX
    @0
    cF
    ffvelrn
    syl2an
    eqeltrrd
    #
    cB
    cA
    cD
    cX
    xmetsym
    syl3anc
    breq1d
    @28
    @6
    @2
    @3
    wa
    #
    @6
    wa
    @7
    @28
    @34
    @6
    @28
    @2
    @3
    wph
    @21
    @31
    @2
    @27
    iscauf.7
    @32
    @21
    @2
    @31
    @21
    @1
    cZ
    @0
    cZ
    cX
    cF
    fdm
    eleq2d
    biimpar
    syl2an
    @33
    jca
    biantrurd
    @2
    @3
    @6
    df-3an
    syl6bbr
    bitrd
    anassrs
    ralbidva
    rexbidva
    ralbidv
    wph
    vx
    cA
    cB
    cD
    vj
    vk
    cF
    cM
    cX
    cZ
    iscau3.2
    iscau3.3
    iscau3.4
    iscau4.5
    iscau4.6
    iscau4
    3bitr4rd
end
