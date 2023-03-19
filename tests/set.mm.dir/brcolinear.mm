include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cop.mm"
include "ccolin.mm"
include "wbr.mm"
include "cv.mm"
include "cbtwn.mm"
include "w3o.mm"
include "wrex.mm"
include "wb.mm"
include "brcolinear2.mm"
include "3adant1.mm"
include "adantl.mm"
include "simpr.mm"
include "rexlimivw.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "3anbi123d.mm"
include "anbi1d.mm"
include "rspcev.mm"
include "expr.mm"
include "impbid2.mm"
include "bitrd.mm"

theorem brcolinear
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N
  let vn: setvar n


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) -> ( A Colinear <. B , C >. <-> ( A Btwn <. B , C >. \/ B Btwn <. C , A >. \/ C Btwn <. A , B >. ) ) )

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
    wa
    #
    cA
    cB
    cC
    cop
    #
    ccolin
    wbr
    #
    cA
    vn
    cv
    #
    cee
    cfv
    #
    wcel
    #
    cB
    @10
    wcel
    #
    cC
    @10
    wcel
    #
    w3a
    #
    cA
    @7
    cbtwn
    wbr
    cB
    cC
    cA
    cop
    cbtwn
    wbr
    cC
    cA
    cB
    cop
    cbtwn
    wbr
    w3o
    #
    wa
    #
    vn
    cn
    wrex
    #
    @15
    @5
    @8
    @17
    wb
    #
    @0
    @3
    @4
    @18
    @2
    cA
    cB
    cC
    vn
    @1
    @1
    brcolinear2
    3adant1
    adantl
    @6
    @17
    @15
    @16
    @15
    vn
    cn
    @14
    @15
    simpr
    rexlimivw
    @0
    @5
    @15
    @17
    @16
    @5
    @15
    wa
    vn
    cN
    cn
    @9
    cN
    wceq
    #
    @14
    @5
    @15
    @19
    @11
    @2
    @12
    @3
    @13
    @4
    @19
    @10
    @1
    cA
    @9
    cN
    cee
    fveq2
    #
    eleq2d
    @19
    @10
    @1
    cB
    @20
    eleq2d
    @19
    @10
    @1
    cC
    @20
    eleq2d
    3anbi123d
    anbi1d
    rspcev
    expr
    impbid2
    bitrd
end
