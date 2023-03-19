include "crab.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "nfrab1.mm"
include "dfss3f.mm"
include "rabidim1.mm"
include "mprgbir.mm"

theorem ssrab2f
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume ssrab2f.1: |- F/_ x A


  assert |- { x e. A | ph } C_ A

  proof
    wph
    vx
    cA
    crab
    #
    cA
    wss
    vx
    cv
    cA
    wcel
    vx
    @0
    vx
    @0
    cA
    wph
    vx
    cA
    nfrab1
    ssrab2f.1
    dfss3f
    wph
    vx
    cA
    rabidim1
    mprgbir
end
