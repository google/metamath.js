include "cfrgr.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "wreu.mm"
include "wa.mm"
include "frcond1.mm"
include "prex.mm"
include "prss.mm"
include "bicomi.mm"
include "reubii.mm"
include "syl6ib.mm"

theorem frcond2
  let cA: class A
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let vb: setvar b
  let vk: setvar k
  let vl: setvar l
  assume frcond1.v: |- V = ( Vtx ` G )
  assume frcond1.e: |- E = ( Edg ` G )

  disjoint A b
  disjoint C b
  disjoint G b
  disjoint V b
  disjoint A k
  disjoint A l
  disjoint b k
  disjoint b l
  disjoint k l
  disjoint C k
  disjoint C l
  disjoint E k
  disjoint E l
  disjoint G k
  disjoint G l
  disjoint V k
  disjoint V l
  assert |- ( G e. FriendGraph -> ( ( A e. V /\ C e. V /\ A =/= C ) -> E! b e. V ( { A , b } e. E /\ { b , C } e. E ) ) )

  proof
    cG
    cfrgr
    wcel
    cA
    cV
    wcel
    cC
    cV
    wcel
    cA
    cC
    wne
    w3a
    cA
    vb
    cv
    #
    cpr
    #
    @0
    cC
    cpr
    #
    cpr
    cE
    wss
    #
    vb
    cV
    wreu
    @1
    cE
    wcel
    @2
    cE
    wcel
    wa
    #
    vb
    cV
    wreu
    cA
    cC
    cE
    cG
    cV
    vb
    frcond1.v
    frcond1.e
    frcond1
    @3
    @4
    vb
    cV
    @4
    @3
    @1
    @2
    cE
    cA
    @0
    prex
    @0
    cC
    prex
    prss
    bicomi
    reubii
    syl6ib
end
