include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "wne.mm"
include "cop.mm"
include "ccolin.mm"
include "wbr.mm"
include "ccgr.mm"
include "wceq.mm"
include "wi.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp3l.mm"
include "3jca.mm"
include "linecgr.mm"
include "syld3an2.mm"
include "simp1.mm"
include "simp3r.mm"
include "cgrid2.mm"
include "syl13anc.mm"
include "syld.mm"

theorem lineid
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> ( ( ( A =/= B /\ A Colinear <. B , C >. ) /\ ( <. A , C >. Cgr <. A , D >. /\ <. B , C >. Cgr <. B , D >. ) ) -> C = D ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    wa
    #
    cC
    @1
    wcel
    #
    cD
    @1
    wcel
    #
    wa
    #
    w3a
    #
    cA
    cB
    wne
    cA
    cB
    cC
    cop
    #
    ccolin
    wbr
    wa
    cA
    cC
    cop
    cA
    cD
    cop
    ccgr
    wbr
    @9
    cB
    cD
    cop
    ccgr
    wbr
    wa
    wa
    #
    cC
    cC
    cop
    cC
    cD
    cop
    ccgr
    wbr
    #
    cC
    cD
    wceq
    #
    @0
    @2
    @3
    @5
    w3a
    @4
    @7
    @10
    @11
    wi
    @8
    @2
    @3
    @5
    @0
    @2
    @3
    @7
    simp2l
    @0
    @2
    @3
    @7
    simp2r
    @0
    @4
    @5
    @6
    simp3l
    #
    3jca
    cA
    cB
    cC
    cC
    cD
    cN
    linecgr
    syld3an2
    @8
    @0
    @5
    @5
    @6
    @11
    @12
    wi
    @0
    @4
    @7
    simp1
    @13
    @13
    @0
    @4
    @5
    @6
    simp3r
    cC
    cC
    cD
    cN
    cgrid2
    syl13anc
    syld
end
