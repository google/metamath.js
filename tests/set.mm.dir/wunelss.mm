include "wtr.mm"
include "wcel.mm"
include "wss.mm"
include "cwun.mm"
include "wuntr.mm"
include "syl.mm"
include "trss.mm"
include "sylc.mm"

theorem wunelss
  let wph: wff ph
  let cA: class A
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let vu: setvar u
  assume wununi.1: |- ( ph -> U e. WUni )
  assume wununi.2: |- ( ph -> A e. U )


  assert |- ( ph -> A C_ U )

  proof
    wph
    cU
    wtr
    #
    cA
    cU
    wcel
    cA
    cU
    wss
    wph
    cU
    cwun
    wcel
    @0
    wununi.1
    cU
    wuntr
    syl
    wununi.2
    cU
    cA
    trss
    sylc
end
