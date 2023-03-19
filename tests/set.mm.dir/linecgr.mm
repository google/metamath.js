include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "cop.mm"
include "ccolin.mm"
include "wbr.mm"
include "ccgr.mm"
include "ccgr3.mm"
include "simprlr.mm"
include "cgr3rflx.mm"
include "3adant3.mm"
include "adantr.mm"
include "simprr.mm"
include "3jca.mm"
include "simprll.mm"
include "jca.mm"
include "ex.mm"
include "wi.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23.mm"
include "simp3l.mm"
include "simp3r.mm"
include "cfs.mm"
include "brfs.mm"
include "anbi1d.mm"
include "fscgr.mm"
include "sylbird.mm"
include "syl333anc.mm"
include "syld.mm"

theorem linecgr
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( P e. ( EE ` N ) /\ Q e. ( EE ` N ) ) ) -> ( ( ( A =/= B /\ A Colinear <. B , C >. ) /\ ( <. A , P >. Cgr <. A , Q >. /\ <. B , P >. Cgr <. B , Q >. ) ) -> <. C , P >. Cgr <. C , Q >. ) )

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
    cC
    @1
    wcel
    #
    w3a
    #
    cP
    @1
    wcel
    #
    cQ
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
    #
    cA
    cB
    cC
    cop
    #
    ccolin
    wbr
    #
    wa
    #
    cA
    cP
    cop
    cA
    cQ
    cop
    ccgr
    wbr
    cB
    cP
    cop
    cB
    cQ
    cop
    ccgr
    wbr
    wa
    #
    wa
    #
    @12
    cA
    @11
    cop
    #
    @16
    ccgr3
    wbr
    #
    @14
    w3a
    #
    @10
    wa
    #
    cC
    cP
    cop
    #
    cC
    cQ
    cop
    #
    ccgr
    wbr
    #
    @9
    @15
    @19
    @9
    @15
    wa
    #
    @18
    @10
    @23
    @12
    @17
    @14
    @9
    @10
    @12
    @14
    simprlr
    @9
    @17
    @15
    @0
    @5
    @17
    @8
    cA
    cB
    cC
    cN
    cgr3rflx
    3adant3
    adantr
    @9
    @13
    @14
    simprr
    3jca
    @9
    @10
    @12
    @14
    simprll
    jca
    ex
    @9
    @0
    @2
    @3
    @4
    @6
    @2
    @3
    @4
    @7
    @19
    @22
    wi
    @0
    @5
    @8
    simp1
    @0
    @2
    @3
    @4
    @8
    simp21
    #
    @0
    @2
    @3
    @4
    @8
    simp22
    #
    @0
    @2
    @3
    @4
    @8
    simp23
    #
    @0
    @5
    @6
    @7
    simp3l
    @24
    @25
    @26
    @0
    @5
    @6
    @7
    simp3r
    @0
    @2
    @3
    w3a
    @4
    @6
    @2
    w3a
    @3
    @4
    @7
    w3a
    w3a
    #
    @19
    cA
    cB
    cop
    #
    @20
    cop
    @28
    @21
    cop
    cfs
    wbr
    #
    @10
    wa
    @22
    @27
    @29
    @18
    @10
    cA
    cB
    cC
    cP
    cA
    cB
    cC
    cQ
    cN
    brfs
    anbi1d
    cA
    cB
    cC
    cP
    cA
    cB
    cC
    cQ
    cN
    fscgr
    sylbird
    syl333anc
    syld
end
