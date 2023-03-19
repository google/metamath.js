include "wcel.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "wf.mm"
include "cvv.mm"
include "f1of.mm"
include "syl.mm"
include "fex.mm"
include "syl2anc.mm"
include "f1oeq1.mm"
include "elabd.mm"
include "hasheqf1oi.mm"
include "sylc.mm"

theorem hasheqf1od
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cU: class U
  let cF: class F
  let vf: setvar f
  assume hasheqf1od.a: |- ( ph -> A e. U )
  assume hasheqf1od.f: |- ( ph -> F : A -1-1-onto-> B )


  assert |- ( ph -> ( # ` A ) = ( # ` B ) )

  proof
    wph
    cA
    cU
    wcel
    #
    cA
    cB
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    cA
    chash
    cfv
    cB
    chash
    cfv
    wceq
    hasheqf1od.a
    wph
    @2
    cA
    cB
    cF
    wf1o
    #
    vf
    cF
    wph
    cA
    cB
    cF
    wf
    #
    @0
    cF
    cvv
    wcel
    wph
    @3
    @4
    hasheqf1od.f
    cA
    cB
    cF
    f1of
    syl
    hasheqf1od.a
    cA
    cB
    cU
    cF
    fex
    syl2anc
    hasheqf1od.f
    cA
    cB
    @1
    cF
    f1oeq1
    elabd
    cA
    cB
    vf
    cU
    hasheqf1oi
    sylc
end
