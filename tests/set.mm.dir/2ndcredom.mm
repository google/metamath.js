include "c2ndc.mm"
include "wcel.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "ctb.mm"
include "wrex.mm"
include "cr.mm"
include "is2ndc.mm"
include "cpw.mm"
include "tgdom.mm"
include "adantr.mm"
include "cn.mm"
include "cen.mm"
include "simpr.mm"
include "nnenom.mm"
include "ensymi.mm"
include "domentr.mm"
include "sylancl.mm"
include "pwdom.mm"
include "syl.mm"
include "rpnnen.mm"
include "domtr.mm"
include "syl2anc.mm"
include "breq1.mm"
include "syl5ibcom.mm"
include "expimpd.mm"
include "rexlimiv.mm"
include "sylbi.mm"

theorem 2ndcredom
  let cJ: class J
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( J e. 2ndc -> J ~<_ RR )

  proof
    cJ
    c2ndc
    wcel
    vx
    cv
    #
    com
    cdom
    wbr
    #
    @0
    ctg
    cfv
    #
    cJ
    wceq
    #
    wa
    #
    vx
    ctb
    wrex
    cJ
    cr
    cdom
    wbr
    #
    vx
    cJ
    is2ndc
    @4
    @5
    vx
    ctb
    @0
    ctb
    wcel
    #
    @1
    @3
    @5
    @6
    @1
    wa
    #
    @2
    cr
    cdom
    wbr
    #
    @3
    @5
    @7
    @2
    @0
    cpw
    #
    cdom
    wbr
    #
    @9
    cr
    cdom
    wbr
    #
    @8
    @6
    @10
    @1
    @0
    ctb
    tgdom
    adantr
    @7
    @9
    cn
    cpw
    #
    cdom
    wbr
    #
    @12
    cr
    cen
    wbr
    @11
    @7
    @0
    cn
    cdom
    wbr
    #
    @13
    @7
    @1
    com
    cn
    cen
    wbr
    @14
    @6
    @1
    simpr
    cn
    com
    nnenom
    ensymi
    @0
    com
    cn
    domentr
    sylancl
    @0
    cn
    pwdom
    syl
    cr
    @12
    rpnnen
    ensymi
    @9
    @12
    cr
    domentr
    sylancl
    @2
    @9
    cr
    domtr
    syl2anc
    @2
    cJ
    cr
    cdom
    breq1
    syl5ibcom
    expimpd
    rexlimiv
    sylbi
end
