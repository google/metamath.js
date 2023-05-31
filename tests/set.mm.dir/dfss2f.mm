include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "dfss2.mm"
include "nfcri.mm"
include "nfim.mm"
include "nfv.mm"
include "weq.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "cbval.mm"
include "bitri.mm"

theorem dfss2f
  param vx: setvar x
  param cA: class A
  param cB: class B
  let vz: setvar z
  assume dfss2f.1: |- F/_ x A
  assume dfss2f.2: |- F/_ x B


  assert |- ( A C_ B <-> A. x ( x e. A -> x e. B ) )

  proof
    cA
    cB
    wss
    vz
    cv
    #
    cA
    wcel
    #
    @0
    cB
    wcel
    #
    wi
    #
    vz
    wal
    vx
    cv
    #
    cA
    wcel
    #
    @4
    cB
    wcel
    #
    wi
    #
    vx
    wal
    vz
    cA
    cB
    dfss2
    @3
    @7
    vz
    vx
    @1
    @2
    vx
    vx
    vz
    cA
    dfss2f.1
    nfcri
    vx
    vz
    cB
    dfss2f.2
    nfcri
    nfim
    @7
    vz
    nfv
    vz
    vx
    weq
    @1
    @5
    @2
    @6
    @0
    @4
    cA
    eleq1
    @0
    @4
    cB
    eleq1
    imbi12d
    cbval
    bitri
end
