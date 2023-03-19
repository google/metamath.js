include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "wcel.mm"
include "cr.mm"
include "wss.mm"
include "cv.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "cbl.mm"
include "co.mm"
include "crp.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "caddc.mm"
include "cxmt.mm"
include "wb.mm"
include "eqid.mm"
include "rexmet.mm"
include "cmopn.mm"
include "tgioo.mm"
include "elmopn2.mm"
include "ax-mp.mm"
include "ssel2.mm"
include "wceq.mm"
include "rpre.mm"
include "bl2ioo.mm"
include "sylan2.mm"
include "sseq1d.mm"
include "rexbidva.mm"
include "syl.mm"
include "ralbidva.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem opnrebl
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( A e. ( topGen ` ran (,) ) <-> ( A C_ RR /\ A. x e. A E. y e. RR+ ( ( x - y ) (,) ( x + y ) ) C_ A ) )

  proof
    cA
    cioo
    crn
    ctg
    cfv
    #
    wcel
    #
    cA
    cr
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cabs
    cmin
    ccom
    cr
    cr
    cxp
    cres
    #
    cbl
    cfv
    co
    #
    cA
    wss
    #
    vy
    crp
    wrex
    #
    vx
    cA
    wral
    #
    wa
    #
    @2
    @3
    @4
    cmin
    co
    @3
    @4
    caddc
    co
    cioo
    co
    #
    cA
    wss
    #
    vy
    crp
    wrex
    #
    vx
    cA
    wral
    #
    wa
    @5
    cr
    cxmt
    cfv
    wcel
    @1
    @10
    wb
    @5
    @5
    eqid
    #
    rexmet
    vx
    vy
    cA
    @5
    @0
    cr
    @5
    @5
    cmopn
    cfv
    #
    @15
    @16
    eqid
    tgioo
    elmopn2
    ax-mp
    @2
    @9
    @14
    @2
    @8
    @13
    vx
    cA
    @2
    @3
    cA
    wcel
    wa
    @3
    cr
    wcel
    #
    @8
    @13
    wb
    cA
    cr
    @3
    ssel2
    @17
    @7
    @12
    vy
    crp
    @17
    @4
    crp
    wcel
    #
    wa
    @6
    @11
    cA
    @18
    @17
    @4
    cr
    wcel
    @6
    @11
    wceq
    @4
    rpre
    @3
    @4
    @5
    @15
    bl2ioo
    sylan2
    sseq1d
    rexbidva
    syl
    ralbidva
    pm5.32i
    bitri
end
