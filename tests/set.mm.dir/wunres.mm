include "cres.mm"
include "wss.mm"
include "resss.mm"
include "a1i.mm"
include "wunss.mm"

theorem wunres
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume wun0.1: |- ( ph -> U e. WUni )
  assume wunop.2: |- ( ph -> A e. U )


  assert |- ( ph -> ( A |` B ) e. U )

  proof
    wph
    cA
    cA
    cB
    cres
    #
    cU
    wun0.1
    wunop.2
    @0
    cA
    wss
    wph
    cA
    cB
    resss
    a1i
    wunss
end
