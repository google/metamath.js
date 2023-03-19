include "cv.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmnf.mm"
include "cc0.mm"
include "cif.mm"
include "caddc.mm"
include "co.mm"
include "cxr.mm"
include "wcel.mm"
include "wral.mm"
include "cxp.mm"
include "cxad.mm"
include "wf.mm"
include "wa.mm"
include "0xr.mm"
include "pnfxr.mm"
include "keepel.mm"
include "a1i.mm"
include "wn.mm"
include "mnfxr.mm"
include "cr.mm"
include "wo.mm"
include "ioran.mm"
include "w3o.mm"
include "elxr.mm"
include "3orass.mm"
include "sylbb.mm"
include "ord.mm"
include "con1d.mm"
include "imp.mm"
include "sylan2br.mm"
include "readdcl.mm"
include "syl2an.mm"
include "rexrd.mm"
include "anassrs.mm"
include "ifclda.mm"
include "an32s.mm"
include "rgen2a.mm"
include "df-xadd.mm"
include "fmpt2.mm"
include "mpbi.mm"

theorem xaddf
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B


  assert |- +e : ( RR* X. RR* ) --> RR*

  proof
    vx
    cv
    #
    cpnf
    wceq
    #
    vy
    cv
    #
    cmnf
    wceq
    #
    cc0
    cpnf
    cif
    #
    @0
    cmnf
    wceq
    #
    @2
    cpnf
    wceq
    #
    cc0
    cmnf
    cif
    #
    @6
    cpnf
    @3
    cmnf
    @0
    @2
    caddc
    co
    #
    cif
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
    cxad
    wf
    @13
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
    @1
    @4
    @11
    cxr
    @4
    cxr
    wcel
    @16
    @1
    wa
    @3
    cc0
    cpnf
    cxr
    0xr
    pnfxr
    keepel
    a1i
    @16
    @1
    wn
    #
    wa
    #
    @5
    @7
    @10
    cxr
    @7
    cxr
    wcel
    @18
    @5
    wa
    @6
    cc0
    cmnf
    cxr
    0xr
    mnfxr
    keepel
    a1i
    @16
    @17
    @5
    wn
    #
    @10
    cxr
    wcel
    #
    @14
    @17
    @19
    wa
    #
    @15
    @20
    @14
    @21
    wa
    #
    @15
    wa
    #
    @6
    cpnf
    @9
    cxr
    cpnf
    cxr
    wcel
    @23
    @6
    wa
    pnfxr
    a1i
    @23
    @6
    wn
    #
    wa
    #
    @3
    cmnf
    @8
    cxr
    cmnf
    cxr
    wcel
    @25
    @3
    wa
    mnfxr
    a1i
    @23
    @24
    @3
    wn
    #
    @8
    cxr
    wcel
    #
    @22
    @15
    @24
    @26
    wa
    #
    @27
    @22
    @15
    @28
    wa
    #
    wa
    @8
    @22
    @0
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    @8
    cr
    wcel
    @29
    @21
    @14
    @1
    @5
    wo
    #
    wn
    #
    @30
    @1
    @5
    ioran
    @14
    @33
    @30
    @14
    @30
    @32
    @14
    @30
    @32
    @14
    @30
    @1
    @5
    w3o
    @30
    @32
    wo
    @0
    elxr
    @30
    @1
    @5
    3orass
    sylbb
    ord
    con1d
    imp
    sylan2br
    @28
    @15
    @6
    @3
    wo
    #
    wn
    #
    @31
    @6
    @3
    ioran
    @15
    @35
    @31
    @15
    @31
    @34
    @15
    @31
    @34
    @15
    @31
    @6
    @3
    w3o
    @31
    @34
    wo
    @2
    elxr
    @31
    @6
    @3
    3orass
    sylbb
    ord
    con1d
    imp
    sylan2br
    @0
    @2
    readdcl
    syl2an
    rexrd
    anassrs
    anassrs
    ifclda
    ifclda
    an32s
    anassrs
    ifclda
    ifclda
    rgen2a
    vx
    vy
    cxr
    cxr
    @12
    cxr
    cxad
    vx
    vy
    df-xadd
    fmpt2
    mpbi
end
