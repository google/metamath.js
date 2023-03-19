include "cn0.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "cin.mm"
include "wcel.mm"
include "wf.mm"
include "ccnv.mm"
include "cima.mm"
include "cfn.mm"
include "inss1.mm"
include "sseli.mm"
include "elmapi.mm"
include "syl.mm"
include "inss2.mm"
include "cv.mm"
include "wceq.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "eleq1d.mm"
include "elab2g.mm"
include "mpbid.mm"
include "jca.mm"

theorem eulerpartlemelr
  let cA: class A
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vk: setvar k
  assume eulerpartlems.r: |- R = { f | ( `' f " NN ) e. Fin }
  assume eulerpartlems.s: |- S = ( f e. ( ( NN0 ^m NN ) i^i R ) |-> sum_ k e. NN ( ( f ` k ) x. k ) )

  disjoint f k
  disjoint A f
  disjoint A k
  disjoint R f
  disjoint R k
  assert |- ( A e. ( ( NN0 ^m NN ) i^i R ) -> ( A : NN --> NN0 /\ ( `' A " NN ) e. Fin ) )

  proof
    cA
    cn0
    cn
    cmap
    co
    #
    cR
    cin
    #
    wcel
    #
    cn
    cn0
    cA
    wf
    #
    cA
    ccnv
    #
    cn
    cima
    #
    cfn
    wcel
    #
    @2
    cA
    @0
    wcel
    @3
    @1
    @0
    cA
    @0
    cR
    inss1
    sseli
    cA
    cn0
    cn
    elmapi
    syl
    @2
    cA
    cR
    wcel
    @6
    @1
    cR
    cA
    @0
    cR
    inss2
    sseli
    vf
    cv
    #
    ccnv
    #
    cn
    cima
    #
    cfn
    wcel
    @6
    vf
    cA
    cR
    @1
    @7
    cA
    wceq
    #
    @9
    @5
    cfn
    @10
    @8
    @4
    cn
    @7
    cA
    cnveq
    imaeq1d
    eleq1d
    eulerpartlems.r
    elab2g
    mpbid
    jca
end
