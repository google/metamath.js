include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "c0g.mm"
include "csupp.mm"
include "cfn.mm"
include "w3a.mm"
include "cv.mm"
include "cvsca.mm"
include "cmpt.mm"
include "wss.mm"
include "simp3.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "3jca.mm"
include "3adant3.mm"
include "scmsuppss.mm"
include "syl.mm"
include "ssfi.mm"
include "syl2anc.mm"

theorem scmsuppfi
  let vv: setvar v
  let cA: class A
  let cR: class R
  let cS: class S
  let cM: class M
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume scmsuppfi.s: |- S = ( Scalar ` M )
  assume scmsuppfi.r: |- R = ( Base ` S )

  disjoint A v
  disjoint M v
  disjoint R v
  disjoint V v
  disjoint k x
  assert |- ( ( ( M e. LMod /\ V e. ~P ( Base ` M ) ) /\ A e. ( R ^m V ) /\ ( A supp ( 0g ` S ) ) e. Fin ) -> ( ( v e. V |-> ( ( A ` v ) ( .s ` M ) v ) ) supp ( 0g ` M ) ) e. Fin )

  proof
    cM
    clmod
    wcel
    #
    cV
    cM
    cbs
    cfv
    cpw
    wcel
    #
    wa
    #
    cA
    cR
    cV
    cmap
    co
    wcel
    #
    cA
    cS
    c0g
    cfv
    csupp
    co
    #
    cfn
    wcel
    #
    w3a
    #
    @5
    vv
    cV
    vv
    cv
    #
    cA
    cfv
    @7
    cM
    cvsca
    cfv
    co
    cmpt
    cM
    c0g
    cfv
    csupp
    co
    #
    @4
    wss
    #
    @8
    cfn
    wcel
    @2
    @3
    @5
    simp3
    @6
    @0
    @1
    @3
    w3a
    #
    @9
    @2
    @3
    @10
    @5
    @2
    @3
    wa
    @0
    @1
    @3
    @0
    @1
    @3
    simpll
    @0
    @1
    @3
    simplr
    @2
    @3
    simpr
    3jca
    3adant3
    vv
    cA
    cR
    cS
    cM
    cV
    scmsuppfi.s
    scmsuppfi.r
    scmsuppss
    syl
    @4
    @8
    ssfi
    syl2anc
end
