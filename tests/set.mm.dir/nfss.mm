include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "dfss3f.mm"
include "nfra1.mm"
include "nfxfr.mm"

theorem nfss
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume dfss2f.1: |- F/_ x A
  assume dfss2f.2: |- F/_ x B


  assert |- F/ x A C_ B

  proof
    cA
    cB
    wss
    vx
    cv
    cB
    wcel
    #
    vx
    cA
    wral
    vx
    vx
    cA
    cB
    dfss2f.1
    dfss2f.2
    dfss3f
    @0
    vx
    cA
    nfra1
    nfxfr
end
