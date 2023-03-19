include "cdif.mm"
include "difssd.mm"
include "wunss.mm"

theorem wundif
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  assume wununi.1: |- ( ph -> U e. WUni )
  assume wununi.2: |- ( ph -> A e. U )


  assert |- ( ph -> ( A \ B ) e. U )

  proof
    wph
    cA
    cA
    cB
    cdif
    cU
    wununi.1
    wununi.2
    wph
    cA
    cB
    difssd
    wunss
end
