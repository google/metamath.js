include "cif.mm"
include "wceq.mm"
include "cfv.mm"
include "fveq2.mm"
include "fvif.mm"
include "syl6eq.mm"

theorem fvifeq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( A = if ( ph , B , C ) -> ( F ` A ) = if ( ph , ( F ` B ) , ( F ` C ) ) )

  proof
    cA
    wph
    cB
    cC
    cif
    #
    wceq
    cA
    cF
    cfv
    @0
    cF
    cfv
    wph
    cB
    cF
    cfv
    cC
    cF
    cfv
    cif
    cA
    @0
    cF
    fveq2
    wph
    cB
    cC
    cF
    fvif
    syl6eq
end
