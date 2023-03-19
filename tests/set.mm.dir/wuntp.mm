include "ctp.mm"
include "csn.mm"
include "cpr.mm"
include "cun.mm"
include "tpass.mm"
include "dfsn2.mm"
include "wunpr.mm"
include "syl5eqel.mm"
include "wunun.mm"

theorem wuntp
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  assume wununi.1: |- ( ph -> U e. WUni )
  assume wununi.2: |- ( ph -> A e. U )
  assume wunpr.3: |- ( ph -> B e. U )
  assume wuntp.3: |- ( ph -> C e. U )


  assert |- ( ph -> { A , B , C } e. U )

  proof
    wph
    cA
    cB
    cC
    ctp
    cA
    csn
    #
    cB
    cC
    cpr
    #
    cun
    cU
    cA
    cB
    cC
    tpass
    wph
    @0
    @1
    cU
    wununi.1
    wph
    @0
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
    wph
    cB
    cC
    cU
    wununi.1
    wunpr.3
    wuntp.3
    wunpr
    wunun
    syl5eqel
end
