include "ccolin.mm"
include "cv.mm"
include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "w3o.mm"
include "wa.mm"
include "cn.mm"
include "wrex.mm"
include "coprab.mm"
include "ccnv.mm"
include "cvv.mm"
include "df-colinear.mm"
include "cxp.mm"
include "ciun.mm"
include "nnex.mm"
include "fvex.mm"
include "xpex.mm"
include "iunex.mm"
include "wceq.mm"
include "wex.mm"
include "cab.mm"
include "df-oprab.mm"
include "opelxpi.mm"
include "3adant1.mm"
include "simp1.mm"
include "syl2anc.mm"
include "adantr.mm"
include "reximi.mm"
include "eliun.mm"
include "sylibr.mm"
include "eleq1.mm"
include "biimpar.mm"
include "sylan2.mm"
include "exlimiv.mm"
include "exlimivv.mm"
include "abssi.mm"
include "eqsstri.mm"
include "ssexi.mm"
include "cnvex.mm"
include "eqeltri.mm"

theorem colinearex
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vn: setvar n
  let vx: setvar x


  assert |- Colinear e. _V

  proof
    ccolin
    va
    cv
    #
    vn
    cv
    #
    cee
    cfv
    #
    wcel
    #
    vb
    cv
    #
    @2
    wcel
    #
    vc
    cv
    #
    @2
    wcel
    #
    w3a
    #
    @0
    @4
    @6
    cop
    #
    cbtwn
    wbr
    @4
    @6
    @0
    cop
    cbtwn
    wbr
    @6
    @0
    @4
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
    vb
    vc
    va
    coprab
    #
    ccnv
    cvv
    vn
    va
    vb
    vc
    df-colinear
    @13
    @13
    vn
    cn
    @2
    @2
    cxp
    #
    @2
    cxp
    #
    ciun
    #
    vn
    cn
    @15
    nnex
    @14
    @2
    @2
    @2
    @1
    cee
    fvex
    #
    @17
    xpex
    @17
    xpex
    iunex
    @13
    vx
    cv
    #
    @9
    @0
    cop
    #
    wceq
    #
    @12
    wa
    #
    va
    wex
    #
    vc
    wex
    vb
    wex
    #
    vx
    cab
    @16
    @12
    vb
    vc
    va
    vx
    df-oprab
    @23
    vx
    @16
    @22
    @18
    @16
    wcel
    #
    vb
    vc
    @21
    @24
    va
    @12
    @20
    @19
    @16
    wcel
    #
    @24
    @12
    @19
    @15
    wcel
    #
    vn
    cn
    wrex
    @25
    @11
    @26
    vn
    cn
    @8
    @26
    @10
    @8
    @9
    @14
    wcel
    #
    @3
    @26
    @5
    @7
    @27
    @3
    @4
    @6
    @2
    @2
    opelxpi
    3adant1
    @3
    @5
    @7
    simp1
    @9
    @0
    @14
    @2
    opelxpi
    syl2anc
    adantr
    reximi
    vn
    @19
    cn
    @15
    eliun
    sylibr
    @20
    @24
    @25
    @18
    @19
    @16
    eleq1
    biimpar
    sylan2
    exlimiv
    exlimivv
    abssi
    eqsstri
    ssexi
    cnvex
    eqeltri
end
