include "cfrgr.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cpr.mm"
include "wa.mm"
include "weu.mm"
include "wreu.mm"
include "frcond2.mm"
include "imp.mm"
include "cusgr.mm"
include "frgrusgr.mm"
include "adantr.mm"
include "simpl.mm"
include "usgrpredgv.mm"
include "simprd.mm"
include "syl2an.mm"
include "reueubd.mm"
include "mpbid.mm"
include "ex.mm"

theorem frgreu
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
  assert |- ( G e. FriendGraph -> ( ( A e. V /\ C e. V /\ A =/= C ) -> E! b ( { A , b } e. E /\ { b , C } e. E ) ) )

  proof
    cG
    cfrgr
    wcel
    #
    cA
    cV
    wcel
    #
    cC
    cV
    wcel
    cA
    cC
    wne
    w3a
    #
    cA
    vb
    cv
    #
    cpr
    cE
    wcel
    #
    @3
    cC
    cpr
    cE
    wcel
    #
    wa
    #
    vb
    weu
    #
    @0
    @2
    wa
    #
    @6
    vb
    cV
    wreu
    #
    @7
    @0
    @2
    @9
    cA
    cC
    cE
    cG
    cV
    vb
    frcond1.v
    frcond1.e
    frcond2
    imp
    @8
    @6
    vb
    cV
    @8
    cG
    cusgr
    wcel
    #
    @4
    @3
    cV
    wcel
    #
    @6
    @0
    @10
    @2
    cG
    frgrusgr
    adantr
    @4
    @5
    simpl
    @10
    @4
    wa
    @1
    @11
    cE
    cG
    cA
    @3
    cV
    frcond1.e
    frcond1.v
    usgrpredgv
    simprd
    syl2an
    reueubd
    mpbid
    ex
end
