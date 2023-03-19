include "c2ndc.mm"
include "wcel.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cfi.mm"
include "cfv.mm"
include "ctg.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "ctb.mm"
include "wrex.mm"
include "is2ndc.mm"
include "df-rex.mm"
include "simprl.mm"
include "wss.mm"
include "ssfii.mm"
include "adantr.mm"
include "cvv.mm"
include "fvex.mm"
include "bastg.mm"
include "fiss.mm"
include "sylancr.mm"
include "ctop.mm"
include "tgcl.mm"
include "fitop.mm"
include "syl.mm"
include "sseqtrd.mm"
include "2basgen.mm"
include "syl2anc.mm"
include "simprr.mm"
include "eqtr3d.mm"
include "jca.mm"
include "eximi.mm"
include "sylbi.mm"
include "fibas.mm"
include "simpl.mm"
include "wb.mm"
include "vex.mm"
include "fictb.mm"
include "ax-mp.mm"
include "sylib.mm"
include "simpr.mm"
include "breq1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "sylibr.mm"
include "exlimiv.mm"
include "impbii.mm"

theorem 2ndcsb
  let vx: setvar x
  let cJ: class J
  let vj: setvar j
  let vy: setvar y
  let cB: class B

  disjoint J x
  disjoint j x
  disjoint j y
  disjoint J j
  disjoint x y
  disjoint J y
  disjoint B x
  assert |- ( J e. 2ndc <-> E. x ( x ~<_ _om /\ ( topGen ` ( fi ` x ) ) = J ) )

  proof
    cJ
    c2ndc
    wcel
    #
    vx
    cv
    #
    com
    cdom
    wbr
    #
    @1
    cfi
    cfv
    #
    ctg
    cfv
    #
    cJ
    wceq
    #
    wa
    #
    vx
    wex
    #
    @0
    @2
    @1
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
    #
    @7
    vx
    cJ
    is2ndc
    @11
    @1
    ctb
    wcel
    #
    @10
    wa
    #
    vx
    wex
    @7
    @10
    vx
    ctb
    df-rex
    @13
    @6
    vx
    @13
    @2
    @5
    @12
    @2
    @9
    simprl
    @13
    @8
    @4
    cJ
    @13
    @1
    @3
    wss
    #
    @3
    @8
    wss
    @8
    @4
    wceq
    @12
    @14
    @10
    @1
    ctb
    ssfii
    adantr
    @13
    @3
    @8
    cfi
    cfv
    #
    @8
    @13
    @8
    cvv
    wcel
    @1
    @8
    wss
    #
    @3
    @15
    wss
    @1
    ctg
    fvex
    @12
    @16
    @10
    @1
    ctb
    bastg
    adantr
    @1
    @8
    cvv
    fiss
    sylancr
    @13
    @8
    ctop
    wcel
    #
    @15
    @8
    wceq
    @12
    @17
    @10
    @1
    tgcl
    adantr
    @8
    fitop
    syl
    sseqtrd
    @1
    @3
    2basgen
    syl2anc
    @12
    @2
    @9
    simprr
    eqtr3d
    jca
    eximi
    sylbi
    sylbi
    @6
    @0
    vx
    @6
    vy
    cv
    #
    com
    cdom
    wbr
    #
    @18
    ctg
    cfv
    #
    cJ
    wceq
    #
    wa
    #
    vy
    ctb
    wrex
    #
    @0
    @6
    @3
    ctb
    wcel
    @3
    com
    cdom
    wbr
    #
    @5
    wa
    #
    @23
    @1
    fibas
    @6
    @24
    @5
    @6
    @2
    @24
    @2
    @5
    simpl
    @1
    cvv
    wcel
    @2
    @24
    wb
    vx
    vex
    @1
    cvv
    fictb
    ax-mp
    sylib
    @2
    @5
    simpr
    jca
    @22
    @25
    vy
    @3
    ctb
    @18
    @3
    wceq
    #
    @19
    @24
    @21
    @5
    @18
    @3
    com
    cdom
    breq1
    @26
    @20
    @4
    cJ
    @18
    @3
    ctg
    fveq2
    eqeq1d
    anbi12d
    rspcev
    sylancr
    vy
    cJ
    is2ndc
    sylibr
    exlimiv
    impbii
end
