include "wfn.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "crn.mm"
include "cxp.mm"
include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "ctex.mm"
include "adantl.mm"
include "cdm.mm"
include "wfun.mm"
include "wb.mm"
include "fndm.mm"
include "eleq1d.mm"
include "adantr.mm"
include "mpbird.mm"
include "fnfun.mm"
include "funrnex.mm"
include "sylc.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "wf.mm"
include "simpl.mm"
include "dffn3.mm"
include "sylib.mm"
include "fssxp.mm"
include "syl.mm"
include "ssdomg.mm"
include "cen.mm"
include "xpdom1g.mm"
include "sylancom.mm"
include "omex.mm"
include "fnrndomg.mm"
include "domtr.mm"
include "xpdom2g.mm"
include "sylancr.mm"
include "xpomen.mm"
include "domentr.mm"
include "sylancl.mm"

theorem fnct
  let cA: class A
  let cF: class F


  assert |- ( ( F Fn A /\ A ~<_ _om ) -> F ~<_ _om )

  proof
    cF
    cA
    wfn
    #
    cA
    com
    cdom
    wbr
    #
    wa
    #
    cF
    cA
    cF
    crn
    #
    cxp
    #
    cdom
    wbr
    #
    @4
    com
    cdom
    wbr
    #
    cF
    com
    cdom
    wbr
    @2
    @4
    cvv
    wcel
    #
    cF
    @4
    wss
    #
    @5
    @2
    cA
    cvv
    wcel
    #
    @3
    cvv
    wcel
    #
    @7
    @1
    @9
    @0
    cA
    ctex
    adantl
    #
    @2
    cF
    cdm
    #
    cvv
    wcel
    #
    cF
    wfun
    #
    @10
    @2
    @13
    @9
    @11
    @0
    @13
    @9
    wb
    @1
    @0
    @12
    cA
    cvv
    cA
    cF
    fndm
    eleq1d
    adantr
    mpbird
    @0
    @14
    @1
    cA
    cF
    fnfun
    adantr
    cvv
    cF
    funrnex
    sylc
    #
    cA
    @3
    cvv
    cvv
    xpexg
    syl2anc
    @2
    cA
    @3
    cF
    wf
    #
    @8
    @2
    @0
    @16
    @0
    @1
    simpl
    #
    cA
    cF
    dffn3
    sylib
    cA
    @3
    cF
    fssxp
    syl
    cF
    @4
    cvv
    ssdomg
    sylc
    @2
    @4
    com
    com
    cxp
    #
    cdom
    wbr
    #
    @18
    com
    cen
    wbr
    @6
    @2
    @4
    com
    @3
    cxp
    #
    cdom
    wbr
    #
    @20
    @18
    cdom
    wbr
    #
    @19
    @0
    @1
    @10
    @21
    @15
    cA
    com
    @3
    cvv
    xpdom1g
    sylancom
    @2
    com
    cvv
    wcel
    @3
    com
    cdom
    wbr
    #
    @22
    omex
    @0
    @1
    @3
    cA
    cdom
    wbr
    #
    @23
    @2
    @9
    @0
    @24
    @11
    @17
    cA
    cvv
    cF
    fnrndomg
    sylc
    @3
    cA
    com
    domtr
    sylancom
    @3
    com
    com
    cvv
    xpdom2g
    sylancr
    @4
    @20
    @18
    domtr
    syl2anc
    xpomen
    @4
    @18
    com
    domentr
    sylancl
    cF
    @4
    com
    domtr
    syl2anc
end
