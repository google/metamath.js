include "cnpi.mm"
include "wcel.mm"
include "cmi.mm"
include "co.mm"
include "cop.mm"
include "ceq.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "oveq2.mm"
include "opeq1d.mm"
include "opeq1.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "opeq2d.mm"
include "opeq2.mm"
include "w3a.mm"
include "mulcompi.mm"
include "oveq2i.mm"
include "mulasspi.mm"
include "3eqtr4i.mm"
include "wb.mm"
include "mulclpi.mm"
include "3adant3.mm"
include "3adant2.mm"
include "3simpc.mm"
include "enqbreq.mm"
include "syl21anc.mm"
include "mpbiri.mm"
include "3expb.mm"
include "expcom.mm"
include "vtocl2ga.mm"
include "impcom.mm"
include "3impb.mm"

theorem mulcanenq
  let cA: class A
  let cB: class B
  let cC: class C
  let vb: setvar b
  let vc: setvar c


  assert |- ( ( A e. N. /\ B e. N. /\ C e. N. ) -> <. ( A .N B ) , ( A .N C ) >. ~Q <. B , C >. )

  proof
    cA
    cnpi
    wcel
    #
    cB
    cnpi
    wcel
    #
    cC
    cnpi
    wcel
    #
    cA
    cB
    cmi
    co
    #
    cA
    cC
    cmi
    co
    #
    cop
    #
    cB
    cC
    cop
    #
    ceq
    wbr
    #
    @1
    @2
    wa
    @0
    @7
    @0
    cA
    vb
    cv
    #
    cmi
    co
    #
    cA
    vc
    cv
    #
    cmi
    co
    #
    cop
    #
    @8
    @10
    cop
    #
    ceq
    wbr
    #
    wi
    @0
    @3
    @11
    cop
    #
    cB
    @10
    cop
    #
    ceq
    wbr
    #
    wi
    @0
    @7
    wi
    vb
    vc
    cB
    cC
    cnpi
    cnpi
    @8
    cB
    wceq
    #
    @14
    @17
    @0
    @18
    @12
    @15
    @13
    @16
    ceq
    @18
    @9
    @3
    @11
    @8
    cB
    cA
    cmi
    oveq2
    opeq1d
    @8
    cB
    @10
    opeq1
    breq12d
    imbi2d
    @10
    cC
    wceq
    #
    @17
    @7
    @0
    @19
    @15
    @5
    @16
    @6
    ceq
    @19
    @11
    @4
    @3
    @10
    cC
    cA
    cmi
    oveq2
    opeq2d
    @10
    cC
    cB
    opeq2
    breq12d
    imbi2d
    @0
    @8
    cnpi
    wcel
    #
    @10
    cnpi
    wcel
    #
    wa
    #
    @14
    @0
    @20
    @21
    @14
    @0
    @20
    @21
    w3a
    #
    @14
    @9
    @10
    cmi
    co
    #
    @11
    @8
    cmi
    co
    #
    wceq
    #
    cA
    @8
    @10
    cmi
    co
    #
    cmi
    co
    cA
    @10
    @8
    cmi
    co
    #
    cmi
    co
    @24
    @25
    @27
    @28
    cA
    cmi
    @8
    @10
    mulcompi
    oveq2i
    cA
    @8
    @10
    mulasspi
    cA
    @10
    @8
    mulasspi
    3eqtr4i
    @23
    @9
    cnpi
    wcel
    #
    @11
    cnpi
    wcel
    #
    @22
    @14
    @26
    wb
    @0
    @20
    @29
    @21
    cA
    @8
    mulclpi
    3adant3
    @0
    @21
    @30
    @20
    cA
    @10
    mulclpi
    3adant2
    @0
    @20
    @21
    3simpc
    @9
    @11
    @8
    @10
    enqbreq
    syl21anc
    mpbiri
    3expb
    expcom
    vtocl2ga
    impcom
    3impb
end
