include "cin.mm"
include "wss.mm"
include "inss1.mm"
include "a1i.mm"
include "wunss.mm"

theorem wunin
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  assume wununi.1: |- ( ph -> U e. WUni )
  assume wununi.2: |- ( ph -> A e. U )


  assert |- ( ph -> ( A i^i B ) e. U )

  proof
    wph
    cA
    cA
    cB
    cin
    #
    cU
    wununi.1
    wununi.2
    @0
    cA
    wss
    wph
    cA
    cB
    inss1
    a1i
    wunss
end
