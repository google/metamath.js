include "cnp.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "cnq.mm"
include "cplq.mm"
include "co.mm"
include "cltq.mm"
include "wbr.mm"
include "crq.mm"
include "cfv.mm"
include "cmq.mm"
include "wb.mm"
include "elprnq.mm"
include "ltrnq.mm"
include "ltmnq.mm"
include "ovex.mm"
include "vex.mm"
include "mulcomnq.mm"
include "caovord2.mm"
include "sylan9bbr.mm"
include "syl5bb.mm"
include "c1q.mm"
include "recidnq.mm"
include "oveq1d.mm"
include "mulidnq.mm"
include "syl5eq.mm"
include "sylan9eqr.mm"
include "breq2d.mm"
include "bitrd.mm"
include "sylan.mm"
include "wi.mm"
include "prcdnq.mm"
include "adantr.mm"
include "sylbid.mm"

theorem addclprlem1
  let vx: setvar x
  let cA: class A
  let vg: setvar g
  let vh: setvar h
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ( ( A e. P. /\ g e. A ) /\ x e. Q. ) -> ( x <Q ( g +Q h ) -> ( ( x .Q ( *Q ` ( g +Q h ) ) ) .Q g ) e. A ) )

  proof
    cA
    cnp
    wcel
    vg
    cv
    #
    cA
    wcel
    wa
    #
    vx
    cv
    #
    cnq
    wcel
    #
    wa
    @2
    @0
    vh
    cv
    cplq
    co
    #
    cltq
    wbr
    #
    @2
    @4
    crq
    cfv
    #
    cmq
    co
    #
    @0
    cmq
    co
    #
    @0
    cltq
    wbr
    #
    @8
    cA
    wcel
    #
    @1
    @0
    cnq
    wcel
    #
    @3
    @5
    @9
    wb
    cA
    @0
    elprnq
    @11
    @3
    wa
    #
    @5
    @8
    @2
    @2
    crq
    cfv
    #
    cmq
    co
    #
    @0
    cmq
    co
    #
    cltq
    wbr
    #
    @9
    @5
    @6
    @13
    cltq
    wbr
    #
    @12
    @16
    @2
    @4
    ltrnq
    @3
    @17
    @7
    @14
    cltq
    wbr
    @11
    @16
    @6
    @13
    @2
    ltmnq
    vy
    vz
    vw
    @7
    @14
    @0
    cltq
    cnq
    cmq
    @2
    @6
    cmq
    ovex
    @2
    @13
    cmq
    ovex
    vy
    cv
    #
    vz
    cv
    #
    vw
    cv
    ltmnq
    vg
    vex
    @18
    @19
    mulcomnq
    caovord2
    sylan9bbr
    syl5bb
    @12
    @15
    @0
    @8
    cltq
    @3
    @11
    @15
    c1q
    @0
    cmq
    co
    #
    @0
    @3
    @14
    c1q
    @0
    cmq
    @2
    recidnq
    oveq1d
    @11
    @20
    @0
    c1q
    cmq
    co
    @0
    c1q
    @0
    mulcomnq
    @0
    mulidnq
    syl5eq
    sylan9eqr
    breq2d
    bitrd
    sylan
    @1
    @9
    @10
    wi
    @3
    cA
    @0
    @8
    prcdnq
    adantr
    sylbid
end
