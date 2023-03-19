include "cort.mm"
include "cfv.mm"
include "cpjh.mm"
include "csn.mm"
include "cspn.mm"
include "chil.mm"
include "wss.mm"
include "ococss.mm"
include "ax-mp.mm"
include "cch.mm"
include "wcel.mm"
include "occl.mm"
include "chssii.mm"
include "pjclii.mm"
include "snssi.mm"
include "spanss.mm"
include "mp2an.mm"
include "csh.mm"
include "wceq.mm"
include "chshii.mm"
include "spanid.mm"
include "sseqtri.mm"
include "pjhclii.mm"
include "spansnchi.mm"
include "chsscon3i.mm"
include "mpbi.mm"
include "sstri.mm"

theorem spansnpji
  let cA: class A
  let cB: class B
  assume spansnpj.1: |- A C_ ~H
  assume spansnpj.2: |- B e. ~H


  assert |- A C_ ( _|_ ` ( span ` { ( ( projh ` ( _|_ ` A ) ) ` B ) } ) )

  proof
    cA
    cA
    cort
    cfv
    #
    cort
    cfv
    #
    cB
    @0
    cpjh
    cfv
    cfv
    #
    csn
    #
    cspn
    cfv
    #
    cort
    cfv
    #
    cA
    chil
    wss
    #
    cA
    @1
    wss
    spansnpj.1
    cA
    ococss
    ax-mp
    @4
    @0
    wss
    @1
    @5
    wss
    @4
    @0
    cspn
    cfv
    #
    @0
    @0
    chil
    wss
    @3
    @0
    wss
    #
    @4
    @7
    wss
    @0
    @6
    @0
    cch
    wcel
    spansnpj.1
    cA
    occl
    ax-mp
    #
    chssii
    @2
    @0
    wcel
    @8
    cB
    @0
    @9
    spansnpj.2
    pjclii
    @2
    @0
    snssi
    ax-mp
    @3
    @0
    spanss
    mp2an
    @0
    csh
    wcel
    @7
    @0
    wceq
    @0
    @9
    chshii
    @0
    spanid
    ax-mp
    sseqtri
    @4
    @0
    @2
    cB
    @0
    @9
    spansnpj.2
    pjhclii
    spansnchi
    @9
    chsscon3i
    mpbi
    sstri
end
