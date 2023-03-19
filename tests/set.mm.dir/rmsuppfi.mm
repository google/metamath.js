include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cmap.mm"
include "co.mm"
include "c0g.mm"
include "cfv.mm"
include "csupp.mm"
include "cfn.mm"
include "cv.mm"
include "cmulr.mm"
include "cmpt.mm"
include "wss.mm"
include "simp3.mm"
include "rmsuppss.mm"
include "3adant3.mm"
include "ssfi.mm"
include "syl2anc.mm"

theorem rmsuppfi
  let vv: setvar v
  let cA: class A
  let cC: class C
  let cR: class R
  let cM: class M
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume rmsuppfi.r: |- R = ( Base ` M )

  disjoint A v
  disjoint C v
  disjoint M v
  disjoint R v
  disjoint X v
  disjoint V v
  disjoint k x
  assert |- ( ( ( M e. Ring /\ V e. X /\ C e. R ) /\ A e. ( R ^m V ) /\ ( A supp ( 0g ` M ) ) e. Fin ) -> ( ( v e. V |-> ( C ( .r ` M ) ( A ` v ) ) ) supp ( 0g ` M ) ) e. Fin )

  proof
    cM
    crg
    wcel
    cV
    cX
    wcel
    cC
    cR
    wcel
    w3a
    #
    cA
    cR
    cV
    cmap
    co
    wcel
    #
    cA
    cM
    c0g
    cfv
    #
    csupp
    co
    #
    cfn
    wcel
    #
    w3a
    @4
    vv
    cV
    cC
    vv
    cv
    cA
    cfv
    cM
    cmulr
    cfv
    co
    cmpt
    @2
    csupp
    co
    #
    @3
    wss
    #
    @5
    cfn
    wcel
    @0
    @1
    @4
    simp3
    @0
    @1
    @6
    @4
    vv
    cA
    cC
    cR
    cM
    cV
    cX
    rmsuppfi.r
    rmsuppss
    3adant3
    @3
    @5
    ssfi
    syl2anc
end
