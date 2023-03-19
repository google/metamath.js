include "cif.mm"
include "cfv.mm"
include "fveq2.mm"
include "ifsb.mm"

theorem fvif
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F ` if ( ph , A , B ) ) = if ( ph , ( F ` A ) , ( F ` B ) )

  proof
    wph
    cA
    cB
    wph
    cA
    cB
    cif
    #
    cF
    cfv
    cA
    cF
    cfv
    cB
    cF
    cfv
    @0
    cA
    cF
    fveq2
    @0
    cB
    cF
    fveq2
    ifsb
end
