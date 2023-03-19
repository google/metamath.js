include "wcel.mm"
include "ciun.mm"
include "wss.mm"
include "cv.mm"
include "wi.mm"
include "nfel.mm"
include "nfiu1.mm"
include "nfss.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "sseq1d.mm"
include "imbi12d.mm"
include "ssiun2.mm"
include "vtoclgf.mm"
include "pm2.43i.mm"

theorem ssiun2sf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ssiun2sf.1: |- F/_ x A
  assume ssiun2sf.2: |- F/_ x C
  assume ssiun2sf.3: |- F/_ x D
  assume ssiun2sf.4: |- ( x = C -> B = D )


  assert |- ( C e. A -> D C_ U_ x e. A B )

  proof
    cC
    cA
    wcel
    #
    cD
    vx
    cA
    cB
    ciun
    #
    wss
    #
    vx
    cv
    #
    cA
    wcel
    #
    cB
    @1
    wss
    #
    wi
    @0
    @2
    wi
    vx
    cC
    cA
    ssiun2sf.2
    @0
    @2
    vx
    vx
    cC
    cA
    ssiun2sf.2
    ssiun2sf.1
    nfel
    vx
    cD
    @1
    ssiun2sf.3
    vx
    cA
    cB
    nfiu1
    nfss
    nfim
    @3
    cC
    wceq
    #
    @4
    @0
    @5
    @2
    @3
    cC
    cA
    eleq1
    @6
    cB
    cD
    @1
    ssiun2sf.4
    sseq1d
    imbi12d
    vx
    cA
    cB
    ssiun2
    vtoclgf
    pm2.43i
end
