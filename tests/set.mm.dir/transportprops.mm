include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cop.mm"
include "ctransport.mm"
include "co.mm"
include "cbtwn.mm"
include "wbr.mm"
include "ccgr.mm"
include "cv.mm"
include "crio.mm"
include "wceq.mm"
include "fvtransport.mm"
include "eqcomd.mm"
include "wreu.mm"
include "wb.mm"
include "transportcl.mm"
include "segconeu.mm"
include "opeq2.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "riota2.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem transportprops
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N
  let vr: setvar r


  assert |- ( ( N e. NN /\ ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) /\ C =/= D ) ) -> ( D Btwn <. C , ( <. A , B >. TransportTo <. C , D >. ) >. /\ <. D , ( <. A , B >. TransportTo <. C , D >. ) >. Cgr <. A , B >. ) )

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
    wa
    cC
    @0
    wcel
    cD
    @0
    wcel
    wa
    cC
    cD
    wne
    w3a
    wa
    #
    cD
    cC
    cA
    cB
    cop
    #
    cC
    cD
    cop
    ctransport
    co
    #
    cop
    #
    cbtwn
    wbr
    #
    cD
    @3
    cop
    #
    @2
    ccgr
    wbr
    #
    wa
    #
    cD
    cC
    vr
    cv
    #
    cop
    #
    cbtwn
    wbr
    #
    cD
    @9
    cop
    #
    @2
    ccgr
    wbr
    #
    wa
    #
    vr
    @0
    crio
    #
    @3
    wceq
    #
    @1
    @3
    @15
    cA
    cB
    cC
    cD
    cN
    vr
    fvtransport
    eqcomd
    @1
    @3
    @0
    wcel
    @14
    vr
    @0
    wreu
    @8
    @16
    wb
    cA
    cB
    cC
    cD
    cN
    transportcl
    cA
    cB
    cC
    cD
    cN
    vr
    segconeu
    @14
    @8
    vr
    @0
    @3
    @9
    @3
    wceq
    #
    @11
    @5
    @13
    @7
    @17
    @10
    @4
    cD
    cbtwn
    @9
    @3
    cC
    opeq2
    breq2d
    @17
    @12
    @6
    @2
    ccgr
    @9
    @3
    cD
    opeq2
    breq1d
    anbi12d
    riota2
    syl2anc
    mpbird
end
