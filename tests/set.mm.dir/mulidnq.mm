include "cnq.mm"
include "wcel.mm"
include "c1q.mm"
include "cmq.mm"
include "co.mm"
include "cmpq.mm"
include "cerq.mm"
include "cfv.mm"
include "wceq.mm"
include "1nq.mm"
include "mulpqnq.mm"
include "mpan2.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "c1o.mm"
include "cmi.mm"
include "cnpi.mm"
include "cxp.mm"
include "wrel.mm"
include "relxp.mm"
include "elpqn.mm"
include "1st2nd.mm"
include "sylancr.mm"
include "df-1nq.mm"
include "a1i.mm"
include "oveq12d.mm"
include "xp1st.mm"
include "syl.mm"
include "xp2nd.mm"
include "1pi.mm"
include "mulpipq.mm"
include "syl22anc.mm"
include "mulidpi.mm"
include "opeq12d.mm"
include "3eqtrd.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "nqerid.mm"

theorem mulidnq
  let cA: class A


  assert |- ( A e. Q. -> ( A .Q 1Q ) = A )

  proof
    cA
    cnq
    wcel
    #
    cA
    c1q
    cmq
    co
    #
    cA
    c1q
    cmpq
    co
    #
    cerq
    cfv
    #
    cA
    cerq
    cfv
    cA
    @0
    c1q
    cnq
    wcel
    @1
    @3
    wceq
    1nq
    cA
    c1q
    mulpqnq
    mpan2
    @0
    @2
    cA
    cerq
    @0
    @2
    cA
    c1st
    cfv
    #
    cA
    c2nd
    cfv
    #
    cop
    #
    cA
    @0
    @2
    @6
    c1o
    c1o
    cop
    #
    cmpq
    co
    #
    @4
    c1o
    cmi
    co
    #
    @5
    c1o
    cmi
    co
    #
    cop
    #
    @6
    @0
    cA
    @6
    c1q
    @7
    cmpq
    @0
    cnpi
    cnpi
    cxp
    #
    wrel
    cA
    @12
    wcel
    #
    cA
    @6
    wceq
    cnpi
    cnpi
    relxp
    cA
    elpqn
    #
    cA
    @12
    1st2nd
    sylancr
    #
    c1q
    @7
    wceq
    @0
    df-1nq
    a1i
    oveq12d
    @0
    @4
    cnpi
    wcel
    #
    @5
    cnpi
    wcel
    #
    c1o
    cnpi
    wcel
    #
    @18
    @8
    @11
    wceq
    @0
    @13
    @16
    @14
    cA
    cnpi
    cnpi
    xp1st
    #
    syl
    @0
    @13
    @17
    @14
    cA
    cnpi
    cnpi
    xp2nd
    #
    syl
    @18
    @0
    1pi
    a1i
    #
    @21
    @4
    @5
    c1o
    c1o
    mulpipq
    syl22anc
    @0
    @13
    @11
    @6
    wceq
    @14
    @13
    @9
    @4
    @10
    @5
    @13
    @16
    @9
    @4
    wceq
    @19
    @4
    mulidpi
    syl
    @13
    @17
    @10
    @5
    wceq
    @20
    @5
    mulidpi
    syl
    opeq12d
    syl
    3eqtrd
    @15
    eqtr4d
    fveq2d
    cA
    nqerid
    3eqtrd
end
