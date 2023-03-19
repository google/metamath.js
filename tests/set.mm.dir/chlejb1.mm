include "cch.mm"
include "wcel.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "c0h.mm"
include "cif.mm"
include "sseq1.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "bibi12d.mm"
include "sseq2.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "h0elch.mm"
include "elimel.mm"
include "chlejb1i.mm"
include "dedth2h.mm"

theorem chlejb1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A C_ B <-> ( A vH B ) = B ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cA
    cB
    wss
    #
    cA
    cB
    chj
    co
    #
    cB
    wceq
    #
    wb
    @0
    cA
    c0h
    cif
    #
    cB
    wss
    #
    @5
    cB
    chj
    co
    #
    cB
    wceq
    #
    wb
    @5
    @1
    cB
    c0h
    cif
    #
    wss
    #
    @5
    @9
    chj
    co
    #
    @9
    wceq
    #
    wb
    cA
    cB
    c0h
    c0h
    cA
    @5
    wceq
    #
    @2
    @6
    @4
    @8
    cA
    @5
    cB
    sseq1
    @13
    @3
    @7
    cB
    cA
    @5
    cB
    chj
    oveq1
    eqeq1d
    bibi12d
    cB
    @9
    wceq
    #
    @6
    @10
    @8
    @12
    cB
    @9
    @5
    sseq2
    @14
    @7
    @11
    cB
    @9
    cB
    @9
    @5
    chj
    oveq2
    @14
    id
    eqeq12d
    bibi12d
    @5
    @9
    cA
    c0h
    cch
    h0elch
    elimel
    cB
    c0h
    cch
    h0elch
    elimel
    chlejb1i
    dedth2h
end
