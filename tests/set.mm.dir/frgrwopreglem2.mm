include "c0.mm"
include "wne.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cfrgr.mm"
include "wcel.mm"
include "c2.mm"
include "cle.mm"
include "cv.mm"
include "wex.mm"
include "wi.mm"
include "n0.mm"
include "wceq.mm"
include "wa.mm"
include "rabeq2i.mm"
include "cvtxdg.mm"
include "vdgfrgrgt2.mm"
include "imp.mm"
include "wb.mm"
include "breq2.mm"
include "fveq1i.mm"
include "breq2i.mm"
include "syl6bb.mm"
include "eqcoms.mm"
include "syl5ibrcom.mm"
include "exp31.mm"
include "com14.mm"
include "impcom.mm"
include "sylbi.mm"
include "exlimiv.mm"
include "3imp31.mm"

theorem frgrwopreglem2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cG: class G
  let cK: class K
  let cV: class V
  assume frgrwopreg.v: |- V = ( Vtx ` G )
  assume frgrwopreg.d: |- D = ( VtxDeg ` G )
  assume frgrwopreg.a: |- A = { x e. V | ( D ` x ) = K }
  assume frgrwopreg.b: |- B = ( V \ A )

  disjoint V x
  disjoint A x
  disjoint G x
  disjoint K x
  assert |- ( ( G e. FriendGraph /\ 1 < ( # ` V ) /\ A =/= (/) ) -> 2 <_ K )

  proof
    cA
    c0
    wne
    #
    c1
    cV
    chash
    cfv
    clt
    wbr
    #
    cG
    cfrgr
    wcel
    #
    c2
    cK
    cle
    wbr
    #
    @0
    vx
    cv
    #
    cA
    wcel
    #
    vx
    wex
    @1
    @2
    @3
    wi
    wi
    #
    vx
    cA
    n0
    @5
    @6
    vx
    @5
    @4
    cV
    wcel
    #
    @4
    cD
    cfv
    #
    cK
    wceq
    #
    wa
    @6
    @9
    vx
    cA
    cV
    frgrwopreg.a
    rabeq2i
    @9
    @7
    @6
    @2
    @7
    @1
    @9
    @3
    @2
    @7
    @1
    @9
    @3
    wi
    @2
    @7
    wa
    #
    @1
    wa
    @3
    @9
    c2
    @4
    cG
    cvtxdg
    cfv
    #
    cfv
    #
    cle
    wbr
    #
    @10
    @1
    @13
    cG
    @4
    cV
    frgrwopreg.v
    vdgfrgrgt2
    imp
    @3
    @13
    wb
    cK
    @8
    cK
    @8
    wceq
    @3
    c2
    @8
    cle
    wbr
    @13
    cK
    @8
    c2
    cle
    breq2
    @8
    @12
    c2
    cle
    @4
    cD
    @11
    frgrwopreg.d
    fveq1i
    breq2i
    syl6bb
    eqcoms
    syl5ibrcom
    exp31
    com14
    impcom
    sylbi
    exlimiv
    sylbi
    3imp31
end
