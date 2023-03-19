include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "crn.mm"
include "cmpt.mm"
include "fconstmpt.mm"
include "eqtr4i.mm"
include "wfn.mm"
include "c0.mm"
include "wne.mm"
include "wb.mm"
include "wf.mm"
include "fmptd.mm"
include "ffn.mm"
include "syl.mm"
include "fconst5.mm"
include "syl2anc.mm"
include "mpbii.mm"

theorem rnmptc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume rnmptc.f: |- F = ( x e. A |-> B )
  assume rnmptc.b: |- ( ( ph /\ x e. A ) -> B e. C )
  assume rnmptc.a: |- ( ph -> A =/= (/) )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint ph x
  assert |- ( ph -> ran F = { B } )

  proof
    wph
    cF
    cA
    cB
    csn
    #
    cxp
    #
    wceq
    #
    cF
    crn
    @0
    wceq
    #
    cF
    vx
    cA
    cB
    cmpt
    @1
    rnmptc.f
    vx
    cA
    cB
    fconstmpt
    eqtr4i
    wph
    cF
    cA
    wfn
    #
    cA
    c0
    wne
    @2
    @3
    wb
    wph
    cA
    cC
    cF
    wf
    @4
    wph
    vx
    cA
    cB
    cC
    cF
    rnmptc.b
    rnmptc.f
    fmptd
    cA
    cC
    cF
    ffn
    syl
    rnmptc.a
    cA
    cB
    cF
    fconst5
    syl2anc
    mpbii
end
