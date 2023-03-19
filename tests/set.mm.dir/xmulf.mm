include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "clt.mm"
include "wbr.mm"
include "cpnf.mm"
include "wa.mm"
include "cmnf.mm"
include "cmul.mm"
include "co.mm"
include "cif.mm"
include "cxr.mm"
include "wcel.mm"
include "wral.mm"
include "cxp.mm"
include "cxmu.mm"
include "wf.mm"
include "0xr.mm"
include "a1i.mm"
include "wn.mm"
include "pnfxr.mm"
include "mnfxr.mm"
include "xmullem.mm"
include "cr.mm"
include "ancom.mm"
include "orcom.mm"
include "notbii.mm"
include "anbi12i.mm"
include "syl2anb.mm"
include "remulcld.mm"
include "rexrd.mm"
include "ifclda.mm"
include "rgen2a.mm"
include "df-xmul.mm"
include "fmpt2.mm"
include "mpbi.mm"

theorem xmulf
  let vx: setvar x
  let vy: setvar y


  assert |- *e : ( RR* X. RR* ) --> RR*

  proof
    vx
    cv
    #
    cc0
    wceq
    #
    vy
    cv
    #
    cc0
    wceq
    #
    wo
    #
    cc0
    cc0
    @2
    clt
    wbr
    #
    @0
    cpnf
    wceq
    #
    wa
    @2
    cc0
    clt
    wbr
    #
    @0
    cmnf
    wceq
    #
    wa
    wo
    #
    cc0
    @0
    clt
    wbr
    #
    @2
    cpnf
    wceq
    #
    wa
    @0
    cc0
    clt
    wbr
    #
    @2
    cmnf
    wceq
    #
    wa
    wo
    #
    wo
    #
    cpnf
    @5
    @8
    wa
    @7
    @6
    wa
    wo
    #
    @10
    @13
    wa
    @12
    @11
    wa
    wo
    #
    wo
    #
    cmnf
    @0
    @2
    cmul
    co
    #
    cif
    #
    cif
    #
    cif
    #
    cxr
    wcel
    #
    vy
    cxr
    wral
    vx
    cxr
    wral
    cxr
    cxr
    cxp
    cxr
    cxmu
    wf
    @23
    vx
    vy
    cxr
    @0
    cxr
    wcel
    #
    @2
    cxr
    wcel
    #
    wa
    #
    @4
    cc0
    @21
    cxr
    cc0
    cxr
    wcel
    @26
    @4
    wa
    0xr
    a1i
    @26
    @4
    wn
    #
    wa
    #
    @15
    cpnf
    @20
    cxr
    cpnf
    cxr
    wcel
    @28
    @15
    wa
    pnfxr
    a1i
    @28
    @15
    wn
    #
    wa
    #
    @18
    cmnf
    @19
    cxr
    cmnf
    cxr
    wcel
    @30
    @18
    wa
    mnfxr
    a1i
    @30
    @18
    wn
    #
    wa
    #
    @19
    @32
    @0
    @2
    @0
    @2
    xmullem
    @30
    @25
    @24
    wa
    #
    @3
    @1
    wo
    #
    wn
    #
    wa
    #
    @14
    @9
    wo
    #
    wn
    #
    wa
    @17
    @16
    wo
    #
    wn
    @2
    cr
    wcel
    @31
    @28
    @36
    @29
    @38
    @26
    @33
    @27
    @35
    @24
    @25
    ancom
    @4
    @34
    @1
    @3
    orcom
    notbii
    anbi12i
    @15
    @37
    @9
    @14
    orcom
    notbii
    anbi12i
    @18
    @39
    @16
    @17
    orcom
    notbii
    @2
    @0
    xmullem
    syl2anb
    remulcld
    rexrd
    ifclda
    ifclda
    ifclda
    rgen2a
    vx
    vy
    cxr
    cxr
    @22
    cxr
    cxmu
    vx
    vy
    df-xmul
    fmpt2
    mpbi
end
