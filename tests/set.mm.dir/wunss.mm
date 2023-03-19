include "cpw.mm"
include "wunpw.mm"
include "wunelss.mm"
include "sselpwd.mm"
include "sseldd.mm"

theorem wunss
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  assume wununi.1: |- ( ph -> U e. WUni )
  assume wununi.2: |- ( ph -> A e. U )
  assume wunss.3: |- ( ph -> B C_ A )


  assert |- ( ph -> B e. U )

  proof
    wph
    cA
    cpw
    #
    cU
    cB
    wph
    @0
    cU
    wununi.1
    wph
    cA
    cU
    wununi.1
    wununi.2
    wunpw
    wunelss
    wph
    cB
    cA
    cU
    wununi.2
    wunss.3
    sselpwd
    sseldd
end
