include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "ccgr.mm"
include "wceq.mm"
include "ccgr3.mm"
include "wb.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr3.mm"
include "simpr2.mm"
include "cgrcom.mm"
include "syl122anc.mm"
include "biimpd.mm"
include "idd.mm"
include "axcgrrflx.mm"
include "3adant3r1.mm"
include "a1d.mm"
include "3jcad.mm"
include "3ancomb.mm"
include "brcgr3.mm"
include "syl3an3br.mm"
include "3anidm23.mm"
include "sylibrd.mm"
include "wi.mm"
include "btwnxfr.mm"
include "sylan2d.mm"
include "a1i.mm"
include "jcad.mm"
include "3anrot.mm"
include "btwnswapid2.mm"
include "sylan2br.mm"
include "syld.mm"

theorem endofsegid
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) -> ( ( B Btwn <. A , C >. /\ <. A , C >. Cgr <. A , B >. ) -> C = B ) )

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
    cB
    cA
    cC
    cop
    #
    cbtwn
    wbr
    #
    @7
    cA
    cB
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    cC
    @9
    cbtwn
    wbr
    #
    @8
    wa
    #
    cC
    cB
    wceq
    #
    @6
    @11
    @12
    @8
    @6
    @10
    cA
    cB
    cC
    cop
    #
    cop
    cA
    cC
    cB
    cop
    #
    cop
    ccgr3
    wbr
    #
    @8
    @12
    @6
    @10
    @9
    @7
    ccgr
    wbr
    #
    @10
    @15
    @16
    ccgr
    wbr
    #
    w3a
    #
    @17
    @6
    @10
    @18
    @10
    @19
    @6
    @10
    @18
    @6
    @0
    @2
    @4
    @2
    @3
    @10
    @18
    wb
    @0
    @5
    simpl
    @0
    @2
    @3
    @4
    simpr1
    #
    @0
    @2
    @3
    @4
    simpr3
    @21
    @0
    @2
    @3
    @4
    simpr2
    cA
    cC
    cA
    cB
    cN
    cgrcom
    syl122anc
    biimpd
    @6
    @10
    idd
    @6
    @19
    @10
    @0
    @3
    @4
    @19
    @2
    cB
    cC
    cN
    axcgrrflx
    3adant3r1
    a1d
    3jcad
    @0
    @5
    @17
    @20
    wb
    #
    @5
    @0
    @5
    @2
    @4
    @3
    w3a
    #
    @22
    @2
    @4
    @3
    3ancomb
    #
    cA
    cB
    cC
    cA
    cC
    cB
    cN
    brcgr3
    syl3an3br
    3anidm23
    sylibrd
    @0
    @5
    @8
    @17
    wa
    @12
    wi
    #
    @5
    @0
    @5
    @23
    @25
    @24
    cA
    cB
    cC
    cA
    cC
    cB
    cN
    btwnxfr
    syl3an3br
    3anidm23
    sylan2d
    @11
    @8
    wi
    @6
    @8
    @10
    simpl
    a1i
    jcad
    @5
    @0
    @4
    @2
    @3
    w3a
    @13
    @14
    wi
    @4
    @2
    @3
    3anrot
    cC
    cA
    cB
    cN
    btwnswapid2
    sylan2br
    syld
end
