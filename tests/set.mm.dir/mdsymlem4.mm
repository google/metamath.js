include "cv.mm"
include "cat.mm"
include "wcel.mm"
include "cdmd.mm"
include "wbr.mm"
include "c0h.mm"
include "wne.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "wss.mm"
include "wrex.mm"
include "cin.mm"
include "wi.mm"
include "mdsymlem2.mm"
include "exp31.mm"
include "com4t.mm"
include "ex.mm"
include "com23.mm"
include "a1d.mm"
include "imp44.mm"
include "com3l.mm"
include "wn.mm"
include "mdsymlem3.mm"
include "anasss.mm"
include "com3r.mm"
include "ancoms.mm"
include "adantlr.mm"
include "adantl.mm"
include "pm2.61d.mm"
include "rexcom.mm"
include "syl6ib.mm"

theorem mdsymlem4
  let cA: class A
  let cB: class B
  let cC: class C
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vc: setvar c
  assume mdsymlem1.1: |- A e. CH
  assume mdsymlem1.2: |- B e. CH
  assume mdsymlem1.3: |- C = ( A vH p )

  disjoint q r
  disjoint C q
  disjoint C r
  disjoint p q
  disjoint p r
  disjoint A p
  disjoint A q
  disjoint A r
  disjoint B p
  disjoint B q
  disjoint B r
  disjoint c p
  disjoint c q
  disjoint c r
  disjoint A c
  disjoint B c
  assert |- ( p e. HAtoms -> ( ( B MH* A /\ ( ( A =/= 0H /\ B =/= 0H ) /\ p C_ ( A vH B ) ) ) -> E. q e. HAtoms E. r e. HAtoms ( p C_ ( q vH r ) /\ ( q C_ A /\ r C_ B ) ) ) )

  proof
    vp
    cv
    #
    cat
    wcel
    #
    cB
    cA
    cdmd
    wbr
    #
    cA
    c0h
    wne
    #
    cB
    c0h
    wne
    #
    wa
    @0
    cA
    cB
    chj
    co
    wss
    #
    wa
    #
    wa
    #
    @0
    vq
    cv
    #
    vr
    cv
    #
    chj
    co
    wss
    @8
    cA
    wss
    @9
    cB
    wss
    wa
    wa
    #
    vq
    cat
    wrex
    vr
    cat
    wrex
    #
    @10
    vr
    cat
    wrex
    vq
    cat
    wrex
    @1
    cB
    cC
    cin
    cA
    wss
    #
    @7
    @11
    wi
    @7
    @1
    @12
    @11
    @2
    @3
    @4
    @5
    @1
    @12
    @11
    wi
    wi
    #
    @2
    @4
    @5
    @13
    wi
    wi
    @3
    @2
    @5
    @4
    @13
    @2
    @5
    @4
    @13
    wi
    @1
    @12
    @2
    @5
    wa
    #
    @4
    @11
    @1
    @12
    @14
    @4
    @11
    wi
    cA
    cB
    cC
    vr
    vq
    vp
    mdsymlem1.1
    mdsymlem1.2
    mdsymlem1.3
    mdsymlem2
    exp31
    com4t
    ex
    com23
    a1d
    imp44
    com3l
    @7
    @1
    @12
    wn
    #
    @11
    @6
    @1
    @15
    @11
    wi
    wi
    #
    @2
    @3
    @5
    @16
    @4
    @5
    @3
    @16
    @1
    @15
    @5
    @3
    wa
    #
    @11
    @1
    @15
    @17
    @11
    @1
    @15
    wa
    @5
    @3
    @11
    cA
    cB
    cC
    vr
    vq
    vp
    mdsymlem1.1
    mdsymlem1.2
    mdsymlem1.3
    mdsymlem3
    anasss
    exp31
    com3r
    ancoms
    adantlr
    adantl
    com3l
    pm2.61d
    @10
    vr
    vq
    cat
    cat
    rexcom
    syl6ib
end
