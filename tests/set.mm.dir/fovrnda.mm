include "wcel.mm"
include "co.mm"
include "cxp.mm"
include "wf.mm"
include "fovrn.mm"
include "syl3an1.mm"
include "3expb.mm"

theorem fovrnda
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  assume fovrnd.1: |- ( ph -> F : ( R X. S ) --> C )


  assert |- ( ( ph /\ ( A e. R /\ B e. S ) ) -> ( A F B ) e. C )

  proof
    wph
    cA
    cR
    wcel
    #
    cB
    cS
    wcel
    #
    cA
    cB
    cF
    co
    cC
    wcel
    #
    wph
    cR
    cS
    cxp
    cC
    cF
    wf
    @0
    @1
    @2
    fovrnd.1
    cA
    cB
    cC
    cR
    cS
    cF
    fovrn
    syl3an1
    3expb
end
