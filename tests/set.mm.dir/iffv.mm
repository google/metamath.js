include "cif.mm"
include "cfv.mm"
include "fveq1.mm"
include "ifsb.mm"

theorem iffv
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cG: class G


  assert |- ( if ( ph , F , G ) ` A ) = if ( ph , ( F ` A ) , ( G ` A ) )

  proof
    wph
    cF
    cG
    cA
    wph
    cF
    cG
    cif
    #
    cfv
    cA
    cF
    cfv
    cA
    cG
    cfv
    cA
    @0
    cF
    fveq1
    cA
    @0
    cG
    fveq1
    ifsb
end
