include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wcel.mm"
include "wpss.mm"
include "cen.mm"
include "wa.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "infn0.mm"
include "n0.mm"
include "sylib.mm"
include "csn.mm"
include "cdif.mm"
include "cvv.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "difexg.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "difsnpss.mm"
include "infdifsn.mm"
include "jca.mm"
include "wceq.mm"
include "psseq1.mm"
include "breq1.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "sylc.mm"
include "exlimddv.mm"

theorem infpss
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( _om ~<_ A -> E. x ( x C. A /\ x ~~ A ) )

  proof
    com
    cA
    cdom
    wbr
    #
    vy
    cv
    #
    cA
    wcel
    #
    vx
    cv
    #
    cA
    wpss
    #
    @3
    cA
    cen
    wbr
    #
    wa
    #
    vx
    wex
    #
    vy
    @0
    cA
    c0
    wne
    @2
    vy
    wex
    cA
    infn0
    vy
    cA
    n0
    sylib
    @0
    @2
    wa
    #
    cA
    @1
    csn
    #
    cdif
    #
    cvv
    wcel
    #
    @10
    cA
    wpss
    #
    @10
    cA
    cen
    wbr
    #
    wa
    #
    @7
    @0
    @11
    @2
    @0
    cA
    cvv
    wcel
    @11
    com
    cA
    cdom
    reldom
    brrelex2i
    cA
    @9
    cvv
    difexg
    syl
    adantr
    @8
    @12
    @13
    @8
    @2
    @12
    @0
    @2
    simpr
    @1
    cA
    difsnpss
    sylib
    @0
    @13
    @2
    cA
    @1
    infdifsn
    adantr
    jca
    @6
    @14
    vx
    @10
    cvv
    @3
    @10
    wceq
    @4
    @12
    @5
    @13
    @3
    @10
    cA
    psseq1
    @3
    @10
    cA
    cen
    breq1
    anbi12d
    spcegv
    sylc
    exlimddv
end
