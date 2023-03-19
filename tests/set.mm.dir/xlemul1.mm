include "cxr.mm"
include "wcel.mm"
include "crp.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "cxmu.mm"
include "co.mm"
include "cc0.mm"
include "wa.mm"
include "wi.mm"
include "rpxr.mm"
include "rpge0.mm"
include "jca.mm"
include "xlemul1a.mm"
include "ex.mm"
include "syl3an3.mm"
include "c1.mm"
include "cdiv.mm"
include "simp1.mm"
include "3ad2ant3.mm"
include "xmulcl.mm"
include "syl2anc.mm"
include "simp2.mm"
include "rpreccl.mm"
include "syl.mm"
include "syl112anc.mm"
include "wceq.mm"
include "xmulass.mm"
include "syl3anc.mm"
include "cmul.mm"
include "cr.mm"
include "rpre.mm"
include "rpred.mm"
include "rexmul.mm"
include "recnd.mm"
include "wne.mm"
include "rpne0.mm"
include "recidd.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "xmulid1.mm"
include "3eqtrd.mm"
include "breq12d.mm"
include "sylibd.mm"
include "impbid.mm"

theorem xlemul1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. RR+ ) -> ( A <_ B <-> ( A *e C ) <_ ( B *e C ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    crp
    wcel
    #
    w3a
    #
    cA
    cB
    cle
    wbr
    #
    cA
    cC
    cxmu
    co
    #
    cB
    cC
    cxmu
    co
    #
    cle
    wbr
    #
    @2
    @0
    @1
    cC
    cxr
    wcel
    #
    cc0
    cC
    cle
    wbr
    #
    wa
    #
    @4
    @7
    wi
    @2
    @8
    @9
    cC
    rpxr
    #
    cC
    rpge0
    jca
    @0
    @1
    @10
    w3a
    @4
    @7
    cA
    cB
    cC
    xlemul1a
    ex
    syl3an3
    @3
    @7
    @5
    c1
    cC
    cdiv
    co
    #
    cxmu
    co
    #
    @6
    @12
    cxmu
    co
    #
    cle
    wbr
    #
    @4
    @3
    @5
    cxr
    wcel
    #
    @6
    cxr
    wcel
    #
    @12
    cxr
    wcel
    #
    cc0
    @12
    cle
    wbr
    #
    @7
    @15
    wi
    @3
    @0
    @8
    @16
    @0
    @1
    @2
    simp1
    #
    @2
    @0
    @8
    @1
    @11
    3ad2ant3
    #
    cA
    cC
    xmulcl
    syl2anc
    @3
    @1
    @8
    @17
    @0
    @1
    @2
    simp2
    #
    @21
    cB
    cC
    xmulcl
    syl2anc
    @3
    @12
    crp
    wcel
    #
    @18
    @2
    @0
    @23
    @1
    cC
    rpreccl
    3ad2ant3
    #
    @12
    rpxr
    syl
    #
    @3
    @23
    @19
    @24
    @12
    rpge0
    syl
    @16
    @17
    @18
    @19
    wa
    w3a
    @7
    @15
    @5
    @6
    @12
    xlemul1a
    ex
    syl112anc
    @3
    @13
    cA
    @14
    cB
    cle
    @3
    @13
    cA
    cC
    @12
    cxmu
    co
    #
    cxmu
    co
    #
    cA
    c1
    cxmu
    co
    #
    cA
    @3
    @0
    @8
    @18
    @13
    @27
    wceq
    @20
    @21
    @25
    cA
    cC
    @12
    xmulass
    syl3anc
    @3
    @26
    c1
    cA
    cxmu
    @3
    @26
    cC
    @12
    cmul
    co
    #
    c1
    @3
    cC
    cr
    wcel
    #
    @12
    cr
    wcel
    @26
    @29
    wceq
    @2
    @0
    @30
    @1
    cC
    rpre
    3ad2ant3
    #
    @3
    @12
    @24
    rpred
    cC
    @12
    rexmul
    syl2anc
    @3
    cC
    @3
    cC
    @31
    recnd
    @2
    @0
    cC
    cc0
    wne
    @1
    cC
    rpne0
    3ad2ant3
    recidd
    eqtrd
    #
    oveq2d
    @3
    @0
    @28
    cA
    wceq
    @20
    cA
    xmulid1
    syl
    3eqtrd
    @3
    @14
    cB
    @26
    cxmu
    co
    #
    cB
    c1
    cxmu
    co
    #
    cB
    @3
    @1
    @8
    @18
    @14
    @33
    wceq
    @22
    @21
    @25
    cB
    cC
    @12
    xmulass
    syl3anc
    @3
    @26
    c1
    cB
    cxmu
    @32
    oveq2d
    @3
    @1
    @34
    cB
    wceq
    @22
    cB
    xmulid1
    syl
    3eqtrd
    breq12d
    sylibd
    impbid
end
