include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "clt.mm"
include "wbr.mm"
include "cpnf.mm"
include "cmnf.mm"
include "cmul.mm"
include "co.mm"
include "cif.mm"
include "cxmu.mm"
include "wn.mm"
include "xmullem.mm"
include "recnd.mm"
include "cr.mm"
include "ancom.mm"
include "orcom.mm"
include "notbii.mm"
include "anbi12i.mm"
include "syl2anb.mm"
include "mulcomd.mm"
include "ifeq2da.mm"
include "wb.mm"
include "a1i.mm"
include "ifbid.mm"
include "eqtrd.mm"
include "xmulval.mm"
include "ancoms.mm"
include "3eqtr4d.mm"

theorem xmulcom
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A *e B ) = ( B *e A ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cA
    cc0
    wceq
    #
    cB
    cc0
    wceq
    #
    wo
    #
    cc0
    cc0
    cB
    clt
    wbr
    #
    cA
    cpnf
    wceq
    #
    wa
    cB
    cc0
    clt
    wbr
    #
    cA
    cmnf
    wceq
    #
    wa
    wo
    #
    cc0
    cA
    clt
    wbr
    #
    cB
    cpnf
    wceq
    #
    wa
    cA
    cc0
    clt
    wbr
    #
    cB
    cmnf
    wceq
    #
    wa
    wo
    #
    wo
    #
    cpnf
    @6
    @9
    wa
    @8
    @7
    wa
    wo
    #
    @11
    @14
    wa
    @13
    @12
    wa
    wo
    #
    wo
    #
    cmnf
    cA
    cB
    cmul
    co
    #
    cif
    #
    cif
    #
    cif
    #
    @4
    @3
    wo
    #
    cc0
    @15
    @10
    wo
    #
    cpnf
    @18
    @17
    wo
    #
    cmnf
    cB
    cA
    cmul
    co
    #
    cif
    #
    cif
    #
    cif
    #
    cA
    cB
    cxmu
    co
    cB
    cA
    cxmu
    co
    #
    @2
    @23
    @5
    cc0
    @29
    cif
    @30
    @2
    @5
    @22
    @29
    cc0
    @2
    @5
    wn
    #
    wa
    #
    @22
    @16
    cpnf
    @28
    cif
    @29
    @33
    @16
    @21
    @28
    cpnf
    @33
    @16
    wn
    #
    wa
    #
    @21
    @19
    cmnf
    @27
    cif
    @28
    @35
    @19
    @20
    @27
    cmnf
    @35
    @19
    wn
    #
    wa
    #
    cA
    cB
    @37
    cA
    cA
    cB
    xmullem
    recnd
    @37
    cB
    @35
    @1
    @0
    wa
    #
    @24
    wn
    #
    wa
    #
    @25
    wn
    #
    wa
    @26
    wn
    cB
    cr
    wcel
    @36
    @33
    @40
    @34
    @41
    @2
    @38
    @32
    @39
    @0
    @1
    ancom
    @5
    @24
    @3
    @4
    orcom
    #
    notbii
    anbi12i
    @16
    @25
    @10
    @15
    orcom
    #
    notbii
    anbi12i
    @19
    @26
    @17
    @18
    orcom
    #
    notbii
    cB
    cA
    xmullem
    syl2anb
    recnd
    mulcomd
    ifeq2da
    @35
    @19
    @26
    cmnf
    @27
    @19
    @26
    wb
    @35
    @44
    a1i
    ifbid
    eqtrd
    ifeq2da
    @33
    @16
    @25
    cpnf
    @28
    @16
    @25
    wb
    @33
    @43
    a1i
    ifbid
    eqtrd
    ifeq2da
    @2
    @5
    @24
    cc0
    @29
    @5
    @24
    wb
    @2
    @42
    a1i
    ifbid
    eqtrd
    cA
    cB
    xmulval
    @1
    @0
    @31
    @30
    wceq
    cB
    cA
    xmulval
    ancoms
    3eqtr4d
end
