include "cmpt.mm"
include "clo1.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "wa.mm"
include "cif.mm"
include "simpr.mm"
include "adantr.mm"
include "ifcld.mm"
include "wb.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "wss.mm"
include "cdm.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "syl.mm"
include "lo1dm.mm"
include "eqsstr3d.mm"
include "simprr.mm"
include "sseldd.mm"
include "maxle.mm"
include "syl3anc.mm"
include "syl6bi.mm"
include "imim1d.mm"
include "adantlr.mm"
include "adantrll.mm"
include "simpl.mm"
include "syl2an.mm"
include "lo1mptrcl.mm"
include "simprll.mm"
include "letr.mm"
include "mpand.mm"
include "expr.mm"
include "adantrd.mm"
include "sylbid.mm"
include "a2d.mm"
include "syld.mm"
include "anassrs.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "breq1.mm"
include "imbi1d.mm"
include "rexralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "ello1mpt.mm"
include "3imtr4d.mm"
include "mpd.mm"

theorem lo1le
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cM: class M
  let cV: class V
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z
  assume lo1le.1: |- ( ph -> M e. RR )
  assume lo1le.2: |- ( ph -> ( x e. A |-> B ) e. <_O(1) )
  assume lo1le.3: |- ( ( ph /\ x e. A ) -> B e. V )
  assume lo1le.4: |- ( ( ph /\ x e. A ) -> C e. RR )
  assume lo1le.5: |- ( ( ph /\ ( x e. A /\ M <_ x ) ) -> C <_ B )

  disjoint A x
  disjoint M x
  disjoint ph x
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint C m
  disjoint C y
  disjoint C z
  disjoint M m
  disjoint M z
  disjoint m ph
  disjoint ph y
  disjoint ph z
  disjoint B m
  disjoint B y
  assert |- ( ph -> ( x e. A |-> C ) e. <_O(1) )

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
    lo1le.2
    wph
    vy
    cv
    #
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
    #
    vx
    cA
    wral
    #
    vm
    cr
    wrex
    #
    vy
    cr
    wrex
    vz
    cv
    #
    @4
    cle
    wbr
    #
    cC
    @6
    cle
    wbr
    #
    wi
    #
    vx
    cA
    wral
    vm
    cr
    wrex
    #
    vz
    cr
    wrex
    #
    @1
    @2
    wph
    @10
    @16
    vy
    cr
    wph
    @3
    cr
    wcel
    #
    wa
    #
    cM
    @3
    cle
    wbr
    #
    @3
    cM
    cif
    #
    cr
    wcel
    @10
    @20
    @4
    cle
    wbr
    #
    @13
    wi
    #
    vx
    cA
    wral
    #
    vm
    cr
    wrex
    #
    @16
    @18
    @19
    @3
    cM
    cr
    wph
    @17
    simpr
    wph
    cM
    cr
    wcel
    #
    @17
    lo1le.1
    adantr
    ifcld
    @18
    @9
    @23
    vm
    cr
    @18
    @6
    cr
    wcel
    #
    wa
    @8
    @22
    vx
    cA
    @18
    @26
    @4
    cA
    wcel
    #
    @8
    @22
    wi
    @18
    @26
    @27
    wa
    #
    wa
    #
    @8
    @21
    @7
    wi
    @22
    @29
    @21
    @5
    @7
    @29
    @21
    cM
    @4
    cle
    wbr
    #
    @5
    wa
    #
    @5
    @29
    @25
    @17
    @4
    cr
    wcel
    @21
    @31
    wb
    wph
    @25
    @17
    @28
    lo1le.1
    ad2antrr
    wph
    @17
    @28
    simplr
    @29
    cA
    cr
    @4
    wph
    cA
    cr
    wss
    @17
    @28
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
    @32
    cA
    wceq
    wph
    @33
    vx
    cA
    lo1le.3
    ralrimiva
    vx
    cA
    cB
    cV
    dmmptg
    syl
    wph
    @1
    @32
    cr
    wss
    lo1le.2
    @0
    lo1dm
    syl
    eqsstr3d
    #
    ad2antrr
    @18
    @26
    @27
    simprr
    sseldd
    cM
    @3
    @4
    maxle
    syl3anc
    #
    @30
    @5
    simpr
    syl6bi
    imim1d
    @29
    @21
    @7
    @13
    @29
    @21
    @31
    @7
    @13
    wi
    #
    @35
    @29
    @30
    @36
    @5
    @18
    @28
    @30
    @36
    @18
    @28
    @30
    wa
    #
    wa
    #
    cC
    cB
    cle
    wbr
    #
    @7
    @13
    @18
    @27
    @30
    @39
    @26
    wph
    @27
    @30
    wa
    @39
    @17
    lo1le.5
    adantlr
    adantrll
    @38
    cC
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @26
    @39
    @7
    wa
    @13
    wi
    @18
    wph
    @27
    @40
    @37
    wph
    @17
    simpl
    #
    @26
    @27
    @30
    simplr
    #
    lo1le.4
    syl2an
    @18
    wph
    @27
    @41
    @37
    @42
    @43
    wph
    vx
    cA
    cB
    cV
    lo1le.3
    lo1le.2
    lo1mptrcl
    #
    syl2an
    @18
    @26
    @27
    @30
    simprll
    cC
    cB
    @6
    letr
    syl3anc
    mpand
    expr
    adantrd
    sylbid
    a2d
    syld
    anassrs
    ralimdva
    reximdva
    @15
    @24
    vz
    @20
    cr
    @11
    @20
    wceq
    #
    @14
    @22
    vm
    vx
    cr
    cA
    @45
    @12
    @21
    @13
    @11
    @20
    @4
    cle
    breq1
    imbi1d
    rexralbidv
    rspcev
    syl6an
    rexlimdva
    wph
    vx
    vy
    cA
    cB
    vm
    @34
    @44
    ello1mpt
    wph
    vx
    vz
    cA
    cC
    vm
    @34
    lo1le.4
    ello1mpt
    3imtr4d
    mpd
end
