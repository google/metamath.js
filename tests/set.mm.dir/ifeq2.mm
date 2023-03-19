include "wceq.mm"
include "crab.mm"
include "wn.mm"
include "cun.mm"
include "cif.mm"
include "rabeq.mm"
include "uneq2d.mm"
include "dfif6.mm"
include "3eqtr4g.mm"

theorem ifeq2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A = B -> if ( ph , C , A ) = if ( ph , C , B ) )

  proof
    cA
    cB
    wceq
    #
    wph
    vx
    cC
    crab
    #
    wph
    wn
    #
    vx
    cA
    crab
    #
    cun
    @1
    @2
    vx
    cB
    crab
    #
    cun
    wph
    cC
    cA
    cif
    wph
    cC
    cB
    cif
    @0
    @3
    @4
    @1
    @2
    vx
    cA
    cB
    rabeq
    uneq2d
    wph
    vx
    cC
    cA
    dfif6
    wph
    vx
    cC
    cB
    dfif6
    3eqtr4g
end
