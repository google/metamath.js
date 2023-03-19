include "cch.mm"
include "wcel.mm"
include "wss.mm"
include "wn.mm"
include "chj.mm"
include "co.mm"
include "wpss.mm"
include "wb.mm"
include "c0h.mm"
include "cif.mm"
include "wceq.mm"
include "sseq2.mm"
include "notbid.mm"
include "id.mm"
include "oveq1.mm"
include "psseq12d.mm"
include "bibi12d.mm"
include "sseq1.mm"
include "oveq2.mm"
include "psseq2d.mm"
include "h0elch.mm"
include "elimel.mm"
include "chnlei.mm"
include "dedth2h.mm"

theorem chnle
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( -. B C_ A <-> A C. ( A vH B ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cB
    cA
    wss
    #
    wn
    #
    cA
    cA
    cB
    chj
    co
    #
    wpss
    #
    wb
    cB
    @0
    cA
    c0h
    cif
    #
    wss
    #
    wn
    #
    @6
    @6
    cB
    chj
    co
    #
    wpss
    #
    wb
    @1
    cB
    c0h
    cif
    #
    @6
    wss
    #
    wn
    #
    @6
    @6
    @11
    chj
    co
    #
    wpss
    #
    wb
    cA
    cB
    c0h
    c0h
    cA
    @6
    wceq
    #
    @3
    @8
    @5
    @10
    @16
    @2
    @7
    cA
    @6
    cB
    sseq2
    notbid
    @16
    cA
    @6
    @4
    @9
    @16
    id
    cA
    @6
    cB
    chj
    oveq1
    psseq12d
    bibi12d
    cB
    @11
    wceq
    #
    @8
    @13
    @10
    @15
    @17
    @7
    @12
    cB
    @11
    @6
    sseq1
    notbid
    @17
    @9
    @14
    @6
    cB
    @11
    @6
    chj
    oveq2
    psseq2d
    bibi12d
    @6
    @11
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
    chnlei
    dedth2h
end
