include "crn.mm"
include "cuni.mm"
include "cfv.mm"
include "wunrn.mm"
include "wununi.mm"
include "wss.mm"
include "fvssunirn.mm"
include "a1i.mm"
include "wunss.mm"

theorem wunfv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume wun0.1: |- ( ph -> U e. WUni )
  assume wunop.2: |- ( ph -> A e. U )


  assert |- ( ph -> ( A ` B ) e. U )

  proof
    wph
    cA
    crn
    #
    cuni
    #
    cB
    cA
    cfv
    #
    cU
    wun0.1
    wph
    @0
    cU
    wun0.1
    wph
    cA
    cU
    wun0.1
    wunop.2
    wunrn
    wununi
    @2
    @1
    wss
    wph
    cA
    cB
    fvssunirn
    a1i
    wunss
end
