include "cmpt.mm"
include "clo1.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "wa.mm"
include "reeanv.mm"
include "wss.mm"
include "wb.mm"
include "cdm.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "syl.mm"
include "lo1dm.mm"
include "eqsstr3d.mm"
include "adantr.mm"
include "rexanre.mm"
include "cc0.mm"
include "cif.mm"
include "simprl.mm"
include "simprr.mm"
include "0re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "remulcld.mm"
include "simplrr.mm"
include "max2.mm"
include "sylancr.mm"
include "lo1mptrcl.mm"
include "adantlr.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "jca.mm"
include "simplrl.mm"
include "max1.mm"
include "lemul12b.mm"
include "syl22anc.mm"
include "sylan2d.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "breq2.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "reximdv.mm"
include "sylbird.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "ello1mpt.mm"
include "rexcom.mm"
include "syl6bb.mm"
include "anbi12d.mm"
include "3imtr4d.mm"
include "mp2and.mm"

theorem lo1mul
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vc: setvar c
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  assume o1add2.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume o1add2.2: |- ( ( ph /\ x e. A ) -> C e. V )
  assume lo1add.3: |- ( ph -> ( x e. A |-> B ) e. <_O(1) )
  assume lo1add.4: |- ( ph -> ( x e. A |-> C ) e. <_O(1) )
  assume lo1mul.5: |- ( ( ph /\ x e. A ) -> 0 <_ B )

  disjoint A x
  disjoint ph x
  disjoint c m
  disjoint c n
  disjoint c p
  disjoint c x
  disjoint A c
  disjoint m n
  disjoint m p
  disjoint m x
  disjoint A m
  disjoint n p
  disjoint n x
  disjoint A n
  disjoint p x
  disjoint A p
  disjoint B c
  disjoint B m
  disjoint B n
  disjoint B p
  disjoint C c
  disjoint C m
  disjoint C n
  disjoint C p
  disjoint c ph
  disjoint m ph
  disjoint n ph
  disjoint p ph
  assert |- ( ph -> ( x e. A |-> ( B x. C ) ) e. <_O(1) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    clo1
    wcel
    #
    vx
    cA
    cC
    cmpt
    clo1
    wcel
    #
    vx
    cA
    cB
    cC
    cmul
    co
    #
    cmpt
    clo1
    wcel
    #
    lo1add.3
    lo1add.4
    wph
    vc
    cv
    vx
    cv
    #
    cle
    wbr
    #
    cB
    vm
    cv
    #
    cle
    wbr
    #
    wi
    vx
    cA
    wral
    #
    vc
    cr
    wrex
    #
    vm
    cr
    wrex
    #
    @6
    cC
    vn
    cv
    #
    cle
    wbr
    #
    wi
    vx
    cA
    wral
    #
    vc
    cr
    wrex
    #
    vn
    cr
    wrex
    #
    wa
    #
    @6
    @3
    vp
    cv
    #
    cle
    wbr
    #
    wi
    #
    vx
    cA
    wral
    #
    vp
    cr
    wrex
    #
    vc
    cr
    wrex
    #
    @1
    @2
    wa
    @4
    @17
    @10
    @15
    wa
    #
    vn
    cr
    wrex
    vm
    cr
    wrex
    wph
    @23
    @10
    @15
    vm
    vn
    cr
    cr
    reeanv
    wph
    @24
    @23
    vm
    vn
    cr
    cr
    wph
    @7
    cr
    wcel
    #
    @12
    cr
    wcel
    #
    wa
    #
    wa
    #
    @24
    @6
    @8
    @13
    wa
    #
    wi
    #
    vx
    cA
    wral
    #
    vc
    cr
    wrex
    #
    @23
    @28
    cA
    cr
    wss
    #
    @32
    @24
    wb
    wph
    @33
    @27
    wph
    cA
    @0
    cdm
    #
    cr
    wph
    cB
    cV
    wcel
    #
    vx
    cA
    wral
    @34
    cA
    wceq
    wph
    @35
    vx
    cA
    o1add2.1
    ralrimiva
    vx
    cA
    cB
    cV
    dmmptg
    syl
    wph
    @1
    @34
    cr
    wss
    lo1add.3
    @0
    lo1dm
    syl
    eqsstr3d
    #
    adantr
    @8
    @13
    cA
    vc
    vx
    rexanre
    syl
    @28
    @31
    @22
    vc
    cr
    @28
    @7
    cc0
    @12
    cle
    wbr
    #
    @12
    cc0
    cif
    #
    cmul
    co
    #
    cr
    wcel
    @31
    @6
    @3
    @39
    cle
    wbr
    #
    wi
    #
    vx
    cA
    wral
    #
    @22
    @28
    @7
    @38
    wph
    @25
    @26
    simprl
    @28
    @26
    cc0
    cr
    wcel
    #
    @38
    cr
    wcel
    #
    wph
    @25
    @26
    simprr
    0re
    @37
    @12
    cc0
    cr
    ifcl
    #
    sylancl
    remulcld
    @28
    @30
    @41
    vx
    cA
    @28
    @5
    cA
    wcel
    #
    wa
    #
    @29
    @40
    @6
    @47
    @13
    cC
    @38
    cle
    wbr
    #
    @8
    @40
    @47
    @13
    @12
    @38
    cle
    wbr
    #
    @48
    @47
    @43
    @26
    @49
    0re
    wph
    @25
    @26
    @46
    simplrr
    #
    cc0
    @12
    max2
    sylancr
    @47
    cC
    cr
    wcel
    #
    @26
    @44
    @13
    @49
    wa
    @48
    wi
    wph
    @46
    @51
    @27
    wph
    vx
    cA
    cC
    cV
    o1add2.2
    lo1add.4
    lo1mptrcl
    #
    adantlr
    #
    @50
    @47
    @26
    @43
    @44
    @50
    0re
    @45
    sylancl
    #
    cC
    @12
    @38
    letr
    syl3anc
    mpan2d
    @47
    cB
    cr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    @25
    @51
    @44
    cc0
    @38
    cle
    wbr
    #
    wa
    @8
    @48
    wa
    @40
    wi
    @47
    @55
    @56
    wph
    @46
    @55
    @27
    wph
    vx
    cA
    cB
    cV
    o1add2.1
    lo1add.3
    lo1mptrcl
    #
    adantlr
    wph
    @46
    @56
    @27
    lo1mul.5
    adantlr
    jca
    wph
    @25
    @26
    @46
    simplrl
    @53
    @47
    @44
    @57
    @54
    @47
    @43
    @26
    @57
    0re
    @50
    cc0
    @12
    max1
    sylancr
    jca
    cB
    @7
    cC
    @38
    lemul12b
    syl22anc
    sylan2d
    imim2d
    ralimdva
    @21
    @42
    vp
    @39
    cr
    @18
    @39
    wceq
    #
    @20
    @41
    vx
    cA
    @59
    @19
    @40
    @6
    @18
    @39
    @3
    cle
    breq2
    imbi2d
    ralbidv
    rspcev
    syl6an
    reximdv
    sylbird
    rexlimdvva
    syl5bir
    wph
    @1
    @11
    @2
    @16
    wph
    @1
    @9
    vm
    cr
    wrex
    vc
    cr
    wrex
    @11
    wph
    vx
    vc
    cA
    cB
    vm
    @36
    @58
    ello1mpt
    @9
    vc
    vm
    cr
    cr
    rexcom
    syl6bb
    wph
    @2
    @14
    vn
    cr
    wrex
    vc
    cr
    wrex
    @16
    wph
    vx
    vc
    cA
    cC
    vn
    @36
    @52
    ello1mpt
    @14
    vc
    vn
    cr
    cr
    rexcom
    syl6bb
    anbi12d
    wph
    vx
    vc
    cA
    @3
    vp
    @36
    wph
    @46
    wa
    cB
    cC
    @58
    @52
    remulcld
    ello1mpt
    3imtr4d
    mp2and
end
