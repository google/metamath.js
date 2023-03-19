include "cpreset.mm"
include "wcel.mm"
include "crn.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "cxp.mm"
include "cin.mm"
include "rneqi.mm"
include "eleq2i.mm"
include "cop.mm"
include "wex.mm"
include "wa.mm"
include "wbr.mm"
include "eqid.mm"
include "prsref.mm"
include "df-br.mm"
include "sylib.mm"
include "simpr.mm"
include "opelxpi.mm"
include "sylancom.mm"
include "elind.mm"
include "vex.mm"
include "wceq.mm"
include "opeq1.mm"
include "eleq1d.mm"
include "spcev.mm"
include "syl.mm"
include "ex.mm"
include "inss2.mm"
include "sseli.mm"
include "opelxp2.mm"
include "exlimiv.mm"
include "impbid1.mm"
include "elrn2.mm"
include "syl6rbbr.mm"
include "syl5bb.mm"
include "eqrdv.mm"

theorem prsrn
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let vx: setvar x
  let vy: setvar y
  assume ordtNEW.b: |- B = ( Base ` K )
  assume ordtNEW.l: |- .<_ = ( ( le ` K ) i^i ( B X. B ) )


  assert |- ( K e. Preset -> ran .<_ = B )

  proof
    cK
    cpreset
    wcel
    #
    vx
    c.le
    crn
    #
    cB
    vx
    cv
    #
    @1
    wcel
    @2
    cK
    cple
    cfv
    #
    cB
    cB
    cxp
    #
    cin
    #
    crn
    #
    wcel
    #
    @0
    @2
    cB
    wcel
    #
    @1
    @6
    @2
    c.le
    @5
    ordtNEW.l
    rneqi
    eleq2i
    @0
    @8
    vy
    cv
    #
    @2
    cop
    #
    @5
    wcel
    #
    vy
    wex
    #
    @7
    @0
    @8
    @12
    @0
    @8
    @12
    @0
    @8
    wa
    #
    @2
    @2
    cop
    #
    @5
    wcel
    #
    @12
    @13
    @3
    @4
    @14
    @13
    @2
    @2
    @3
    wbr
    @14
    @3
    wcel
    cB
    cK
    @3
    @2
    ordtNEW.b
    @3
    eqid
    prsref
    @2
    @2
    @3
    df-br
    sylib
    @0
    @8
    @8
    @14
    @4
    wcel
    @0
    @8
    simpr
    @2
    @2
    cB
    cB
    opelxpi
    sylancom
    elind
    @11
    @15
    vy
    @2
    vx
    vex
    #
    @9
    @2
    wceq
    @10
    @14
    @5
    @9
    @2
    @2
    opeq1
    eleq1d
    spcev
    syl
    ex
    @11
    @8
    vy
    @11
    @10
    @4
    wcel
    @8
    @5
    @4
    @10
    @3
    @4
    inss2
    sseli
    @9
    @2
    cB
    cB
    opelxp2
    syl
    exlimiv
    impbid1
    vy
    @2
    @5
    @16
    elrn2
    syl6rbbr
    syl5bb
    eqrdv
end
