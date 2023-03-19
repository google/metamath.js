include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cop.mm"
include "cofs.mm"
include "wbr.mm"
include "wne.mm"
include "wa.mm"
include "cbtwn.mm"
include "ccgr.mm"
include "brofs.mm"
include "anbi1d.mm"
include "simpr.mm"
include "simpl1l.mm"
include "simpl1r.mm"
include "3jca.mm"
include "simpl2.mm"
include "simpl3.mm"
include "syl6bi.mm"
include "ax5seg.mm"
include "syld.mm"

theorem 5segofs
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cN: class N


  assert |- ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ E e. ( EE ` N ) ) /\ ( F e. ( EE ` N ) /\ G e. ( EE ` N ) /\ H e. ( EE ` N ) ) ) -> ( ( <. <. A , B >. , <. C , D >. >. OuterFiveSeg <. <. E , F >. , <. G , H >. >. /\ A =/= B ) -> <. C , D >. Cgr <. G , H >. ) )

  proof
    cN
    cn
    wcel
    cA
    cN
    cee
    cfv
    #
    wcel
    cB
    @0
    wcel
    w3a
    cC
    @0
    wcel
    cD
    @0
    wcel
    cE
    @0
    wcel
    w3a
    cF
    @0
    wcel
    cG
    @0
    wcel
    cH
    @0
    wcel
    w3a
    w3a
    #
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    cop
    cE
    cF
    cop
    #
    cG
    cH
    cop
    #
    cop
    cofs
    wbr
    #
    cA
    cB
    wne
    #
    wa
    #
    @7
    cB
    cA
    cC
    cop
    cbtwn
    wbr
    #
    cF
    cE
    cG
    cop
    cbtwn
    wbr
    #
    w3a
    #
    @2
    @4
    ccgr
    wbr
    cB
    cC
    cop
    cF
    cG
    cop
    ccgr
    wbr
    wa
    #
    cA
    cD
    cop
    cE
    cH
    cop
    ccgr
    wbr
    cB
    cD
    cop
    cF
    cH
    cop
    ccgr
    wbr
    wa
    #
    w3a
    #
    @3
    @5
    ccgr
    wbr
    @1
    @8
    @9
    @10
    wa
    #
    @12
    @13
    w3a
    #
    @7
    wa
    #
    @14
    @1
    @6
    @16
    @7
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    cH
    cN
    brofs
    anbi1d
    @17
    @11
    @12
    @13
    @17
    @7
    @9
    @10
    @16
    @7
    simpr
    @9
    @10
    @12
    @13
    @7
    simpl1l
    @9
    @10
    @12
    @13
    @7
    simpl1r
    3jca
    @15
    @12
    @13
    @7
    simpl2
    @15
    @12
    @13
    @7
    simpl3
    3jca
    syl6bi
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    cH
    cN
    ax5seg
    syld
end
