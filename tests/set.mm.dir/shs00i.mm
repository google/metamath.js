include "c0h.mm"
include "wceq.mm"
include "wa.mm"
include "cph.mm"
include "co.mm"
include "oveq12.mm"
include "h0elsh.mm"
include "shs0i.mm"
include "syl6eq.mm"
include "wss.mm"
include "shsub1i.mm"
include "sseq2.mm"
include "mpbii.mm"
include "csh.mm"
include "wcel.mm"
include "wb.mm"
include "shle0.mm"
include "ax-mp.mm"
include "sylib.mm"
include "shsub2i.mm"
include "jca.mm"
include "impbii.mm"

theorem shs00i
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume shne0.1: |- A e. SH
  assume shs00.2: |- B e. SH


  assert |- ( ( A = 0H /\ B = 0H ) <-> ( A +H B ) = 0H )

  proof
    cA
    c0h
    wceq
    #
    cB
    c0h
    wceq
    #
    wa
    #
    cA
    cB
    cph
    co
    #
    c0h
    wceq
    #
    @2
    @3
    c0h
    c0h
    cph
    co
    c0h
    cA
    c0h
    cB
    c0h
    cph
    oveq12
    c0h
    h0elsh
    shs0i
    syl6eq
    @4
    @0
    @1
    @4
    cA
    c0h
    wss
    #
    @0
    @4
    cA
    @3
    wss
    @5
    cA
    cB
    shne0.1
    shs00.2
    shsub1i
    @3
    c0h
    cA
    sseq2
    mpbii
    cA
    csh
    wcel
    @5
    @0
    wb
    shne0.1
    cA
    shle0
    ax-mp
    sylib
    @4
    cB
    c0h
    wss
    #
    @1
    @4
    cB
    @3
    wss
    @6
    cB
    cA
    shs00.2
    shne0.1
    shsub2i
    @3
    c0h
    cB
    sseq2
    mpbii
    cB
    csh
    wcel
    @6
    @1
    wb
    shs00.2
    cB
    shle0
    ax-mp
    sylib
    jca
    impbii
end
