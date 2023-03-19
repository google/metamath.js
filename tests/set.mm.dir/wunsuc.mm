include "csuc.mm"
include "csn.mm"
include "cun.mm"
include "df-suc.mm"
include "wunsn.mm"
include "wunun.mm"
include "syl5eqel.mm"

theorem wunsuc
  let wph: wff ph
  let cA: class A
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let vu: setvar u
  assume wununi.1: |- ( ph -> U e. WUni )
  assume wununi.2: |- ( ph -> A e. U )


  assert |- ( ph -> suc A e. U )

  proof
    wph
    cA
    csuc
    cA
    cA
    csn
    #
    cun
    cU
    cA
    df-suc
    wph
    cA
    @0
    cU
    wununi.1
    wununi.2
    wph
    cA
    cU
    wununi.1
    wununi.2
    wunsn
    wunun
    syl5eqel
end
