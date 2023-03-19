include "cotp.mm"
include "cop.mm"
include "df-ot.mm"
include "wunop.mm"
include "syl5eqel.mm"

theorem wunot
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume wun0.1: |- ( ph -> U e. WUni )
  assume wunop.2: |- ( ph -> A e. U )
  assume wunop.3: |- ( ph -> B e. U )
  assume wunot.3: |- ( ph -> C e. U )


  assert |- ( ph -> <. A , B , C >. e. U )

  proof
    wph
    cA
    cB
    cC
    cotp
    cA
    cB
    cop
    #
    cC
    cop
    cU
    cA
    cB
    cC
    df-ot
    wph
    @0
    cC
    cU
    wun0.1
    wph
    cA
    cB
    cU
    wun0.1
    wunop.2
    wunop.3
    wunop
    wunot.3
    wunop
    syl5eqel
end
