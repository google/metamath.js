include "csn.mm"
include "cpr.mm"
include "dfsn2.mm"
include "wunpr.mm"
include "syl5eqel.mm"

theorem wunsn
  let wph: wff ph
  let cA: class A
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let vu: setvar u
  assume wununi.1: |- ( ph -> U e. WUni )
  assume wununi.2: |- ( ph -> A e. U )


  assert |- ( ph -> { A } e. U )

  proof
    wph
    cA
    csn
    cA
    cA
    cpr
    cU
    cA
    dfsn2
    wph
    cA
    cA
    cU
    wununi.1
    wununi.2
    wununi.2
    wunpr
    syl5eqel
end
