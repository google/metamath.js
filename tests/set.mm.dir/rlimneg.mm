include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cmpt.mm"
include "cneg.mm"
include "crli.mm"
include "cc.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "0cnd.mm"
include "rlimmptrcl.mm"
include "cr.mm"
include "wss.mm"
include "wbr.mm"
include "cdm.mm"
include "wral.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "syl.mm"
include "rlimss.mm"
include "eqsstr3d.mm"
include "0cn.mm"
include "rlimconst.mm"
include "sylancl.mm"
include "rlimsub.mm"
include "df-neg.mm"
include "mpteq2i.mm"
include "3brtr4g.mm"

theorem rlimneg
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  assume rlimneg.1: |- ( ( ph /\ k e. A ) -> B e. V )
  assume rlimneg.2: |- ( ph -> ( k e. A |-> B ) ~~>r C )

  disjoint A k
  disjoint C k
  disjoint k ph
  assert |- ( ph -> ( k e. A |-> -u B ) ~~>r -u C )

  proof
    wph
    vk
    cA
    cc0
    cB
    cmin
    co
    #
    cmpt
    cc0
    cC
    cmin
    co
    vk
    cA
    cB
    cneg
    #
    cmpt
    cC
    cneg
    crli
    wph
    vk
    cA
    cc0
    cB
    cc0
    cC
    cc
    wph
    vk
    cv
    cA
    wcel
    wa
    0cnd
    wph
    cA
    cB
    cC
    vk
    cV
    rlimneg.1
    rlimneg.2
    rlimmptrcl
    wph
    cA
    cr
    wss
    cc0
    cc
    wcel
    vk
    cA
    cc0
    cmpt
    cc0
    crli
    wbr
    wph
    cA
    vk
    cA
    cB
    cmpt
    #
    cdm
    #
    cr
    wph
    cB
    cV
    wcel
    #
    vk
    cA
    wral
    @3
    cA
    wceq
    wph
    @4
    vk
    cA
    rlimneg.1
    ralrimiva
    vk
    cA
    cB
    cV
    dmmptg
    syl
    wph
    @2
    cC
    crli
    wbr
    @3
    cr
    wss
    rlimneg.2
    cC
    @2
    rlimss
    syl
    eqsstr3d
    0cn
    vk
    cA
    cc0
    rlimconst
    sylancl
    rlimneg.2
    rlimsub
    vk
    cA
    @1
    @0
    cB
    df-neg
    mpteq2i
    cC
    df-neg
    3brtr4g
end
