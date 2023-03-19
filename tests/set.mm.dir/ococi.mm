include "cort.mm"
include "cfv.mm"
include "csh.mm"
include "wcel.mm"
include "chshii.mm"
include "shocsh.mm"
include "ax-mp.mm"
include "wss.mm"
include "shococss.mm"
include "cin.mm"
include "c0h.mm"
include "incom.mm"
include "wceq.mm"
include "ocin.mm"
include "eqtri.mm"
include "omlsii.mm"
include "eqcomi.mm"

theorem ococi
  let cA: class A
  assume ococ.1: |- A e. CH


  assert |- ( _|_ ` ( _|_ ` A ) ) = A

  proof
    cA
    cA
    cort
    cfv
    #
    cort
    cfv
    #
    cA
    @1
    ococ.1
    @0
    csh
    wcel
    #
    @1
    csh
    wcel
    cA
    csh
    wcel
    #
    @2
    cA
    ococ.1
    chshii
    #
    cA
    shocsh
    ax-mp
    #
    @0
    shocsh
    ax-mp
    @3
    cA
    @1
    wss
    @4
    cA
    shococss
    ax-mp
    @1
    @0
    cin
    @0
    @1
    cin
    #
    c0h
    @1
    @0
    incom
    @2
    @6
    c0h
    wceq
    @5
    @0
    ocin
    ax-mp
    eqtri
    omlsii
    eqcomi
end
