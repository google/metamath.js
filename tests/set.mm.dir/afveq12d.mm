include "wdfat.mm"
include "cfv.mm"
include "cvv.mm"
include "cif.mm"
include "cafv.mm"
include "dfateq12d.mm"
include "fveq12d.mm"
include "ifbieq1d.mm"
include "dfafv2.mm"
include "3eqtr4g.mm"

theorem afveq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vx: setvar x
  assume afveq12d.1: |- ( ph -> F = G )
  assume afveq12d.2: |- ( ph -> A = B )


  assert |- ( ph -> ( F ''' A ) = ( G ''' B ) )

  proof
    wph
    cA
    cF
    wdfat
    #
    cA
    cF
    cfv
    #
    cvv
    cif
    cB
    cG
    wdfat
    #
    cB
    cG
    cfv
    #
    cvv
    cif
    cA
    cF
    cafv
    cB
    cG
    cafv
    wph
    @0
    @2
    @1
    @3
    cvv
    wph
    cA
    cB
    cF
    cG
    afveq12d.1
    afveq12d.2
    dfateq12d
    wph
    cA
    cB
    cF
    cG
    afveq12d.1
    afveq12d.2
    fveq12d
    ifbieq1d
    cA
    cF
    dfafv2
    cB
    cG
    dfafv2
    3eqtr4g
end
