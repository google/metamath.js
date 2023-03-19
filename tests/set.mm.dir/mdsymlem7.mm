include "c0h.mm"
include "wne.mm"
include "wa.mm"
include "cdmd.mm"
include "wbr.mm"
include "cv.mm"
include "chj.mm"
include "co.mm"
include "wss.mm"
include "cat.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "mdsymlem4.mm"
include "exp4d.mm"
include "com13.mm"
include "ralrimdv.mm"
include "mdsymlem6.mm"
include "impbid1.mm"

theorem mdsymlem7
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
  assert |- ( ( A =/= 0H /\ B =/= 0H ) -> ( B MH* A <-> A. p e. HAtoms ( p C_ ( A vH B ) -> E. q e. HAtoms E. r e. HAtoms ( p C_ ( q vH r ) /\ ( q C_ A /\ r C_ B ) ) ) ) )

  proof
    cA
    c0h
    wne
    cB
    c0h
    wne
    wa
    #
    cB
    cA
    cdmd
    wbr
    #
    vp
    cv
    #
    cA
    cB
    chj
    co
    wss
    #
    @2
    vq
    cv
    #
    vr
    cv
    #
    chj
    co
    wss
    @4
    cA
    wss
    @5
    cB
    wss
    wa
    wa
    vr
    cat
    wrex
    vq
    cat
    wrex
    #
    wi
    #
    vp
    cat
    wral
    @0
    @1
    @7
    vp
    cat
    @2
    cat
    wcel
    #
    @1
    @0
    @7
    @8
    @1
    @0
    @3
    @6
    cA
    cB
    cC
    vr
    vq
    vp
    mdsymlem1.1
    mdsymlem1.2
    mdsymlem1.3
    mdsymlem4
    exp4d
    com13
    ralrimdv
    cA
    cB
    cC
    vr
    vq
    vp
    mdsymlem1.1
    mdsymlem1.2
    mdsymlem1.3
    mdsymlem6
    impbid1
end
