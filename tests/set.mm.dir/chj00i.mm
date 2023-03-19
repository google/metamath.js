include "c0h.mm"
include "wceq.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "oveq12.mm"
include "h0elch.mm"
include "chj0i.mm"
include "syl6eq.mm"
include "wss.mm"
include "chub1i.mm"
include "sseq2.mm"
include "mpbii.mm"
include "chle0i.mm"
include "sylib.mm"
include "chub2i.mm"
include "jca.mm"
include "impbii.mm"

theorem chj00i
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH


  assert |- ( ( A = 0H /\ B = 0H ) <-> ( A vH B ) = 0H )

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
    chj
    co
    #
    c0h
    wceq
    #
    @2
    @3
    c0h
    c0h
    chj
    co
    c0h
    cA
    c0h
    cB
    c0h
    chj
    oveq12
    c0h
    h0elch
    chj0i
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
    ch0le.1
    chjcl.2
    chub1i
    @3
    c0h
    cA
    sseq2
    mpbii
    cA
    ch0le.1
    chle0i
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
    chjcl.2
    ch0le.1
    chub2i
    @3
    c0h
    cB
    sseq2
    mpbii
    cB
    chjcl.2
    chle0i
    sylib
    jca
    impbii
end
