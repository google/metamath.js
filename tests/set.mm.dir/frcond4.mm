include "cfrgr.mm"
include "wcel.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "cin.mm"
include "csn.mm"
include "wceq.mm"
include "wrex.mm"
include "cdif.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "frcond3.mm"
include "eldifsn.mm"
include "necom.mm"
include "biimpi.mm"
include "anim2i.mm"
include "sylbi.mm"
include "3anass.mm"
include "sylibr.mm"
include "impel.mm"
include "ralrimivva.mm"

theorem frcond4
  let vx: setvar x
  let vk: setvar k
  let cE: class E
  let cG: class G
  let cV: class V
  let vl: setvar l
  let cA: class A
  let vb: setvar b
  let cC: class C
  assume frcond1.v: |- V = ( Vtx ` G )
  assume frcond1.e: |- E = ( Edg ` G )

  disjoint k l
  disjoint E k
  disjoint E l
  disjoint G k
  disjoint G l
  disjoint V k
  disjoint V l
  disjoint E x
  disjoint G x
  disjoint V x
  disjoint k x
  disjoint l x
  disjoint A b
  disjoint A k
  disjoint A l
  disjoint b k
  disjoint b l
  disjoint C b
  disjoint C k
  disjoint C l
  disjoint G b
  disjoint V b
  disjoint A x
  disjoint C x
  disjoint E b
  disjoint b x
  assert |- ( G e. FriendGraph -> A. k e. V A. l e. ( V \ { k } ) E. x e. V ( ( G NeighbVtx k ) i^i ( G NeighbVtx l ) ) = { x } )

  proof
    cG
    cfrgr
    wcel
    #
    cG
    vk
    cv
    #
    cnbgr
    co
    cG
    vl
    cv
    #
    cnbgr
    co
    cin
    vx
    cv
    csn
    wceq
    vx
    cV
    wrex
    #
    vk
    vl
    cV
    cV
    @1
    csn
    cdif
    #
    @0
    @1
    cV
    wcel
    #
    @2
    cV
    wcel
    #
    @1
    @2
    wne
    #
    w3a
    #
    @3
    @5
    @2
    @4
    wcel
    #
    wa
    #
    vx
    @1
    @2
    cE
    cG
    cV
    frcond1.v
    frcond1.e
    frcond3
    @10
    @5
    @6
    @7
    wa
    #
    wa
    @8
    @9
    @11
    @5
    @9
    @6
    @2
    @1
    wne
    #
    wa
    @11
    @2
    cV
    @1
    eldifsn
    @12
    @7
    @6
    @12
    @7
    @2
    @1
    necom
    biimpi
    anim2i
    sylbi
    anim2i
    @5
    @6
    @7
    3anass
    sylibr
    impel
    ralrimivva
end
