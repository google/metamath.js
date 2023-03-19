include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "csgn.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "simpr.mm"
include "rpred.mm"
include "sgnmul.mm"
include "syldan.mm"
include "cxr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "rpxrd.mm"
include "rpgt0d.mm"
include "sgnp.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "simpl.mm"
include "sgnclre.mm"
include "ax-1rid.mm"
include "3syl.mm"
include "3eqtrd.mm"

theorem sgnmulrp2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR+ ) -> ( sgn ` ( A x. B ) ) = ( sgn ` A ) )

  proof
    cA
    cr
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    #
    cA
    cB
    cmul
    co
    csgn
    cfv
    #
    cA
    csgn
    cfv
    #
    cB
    csgn
    cfv
    #
    cmul
    co
    #
    @4
    c1
    cmul
    co
    #
    @4
    @0
    @1
    cB
    cr
    wcel
    @3
    @6
    wceq
    @2
    cB
    @0
    @1
    simpr
    #
    rpred
    cA
    cB
    sgnmul
    syldan
    @2
    @5
    c1
    @4
    cmul
    @2
    cB
    cxr
    wcel
    cc0
    cB
    clt
    wbr
    @5
    c1
    wceq
    @2
    cB
    @8
    rpxrd
    @2
    cB
    @8
    rpgt0d
    cB
    sgnp
    syl2anc
    oveq2d
    @2
    @0
    @4
    cr
    wcel
    @7
    @4
    wceq
    @0
    @1
    simpl
    cA
    sgnclre
    @4
    ax-1rid
    3syl
    3eqtrd
end
