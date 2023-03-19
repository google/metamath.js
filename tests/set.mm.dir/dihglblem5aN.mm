include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "simpr.mm"
include "clat.mm"
include "wb.mm"
include "hllat.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "lhpbase.mm"
include "ad3antlr.mm"
include "eqid.mm"
include "latleeqm1.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "fveq2d.mm"
include "wss.mm"
include "simpll.mm"
include "dihord.mm"
include "mpbird.mm"
include "df-ss.mm"
include "sylib.mm"
include "eqtr4d.mm"
include "wn.mm"
include "catm.mm"
include "coc.mm"
include "ctrl.mm"
include "cltrn.mm"
include "ctendo.mm"
include "cv.mm"
include "crio.mm"
include "cjn.mm"
include "cid.mm"
include "cres.mm"
include "cmpt.mm"
include "dihglblem5apreN.mm"
include "anassrs.mm"
include "pm2.61dan.mm"

theorem dihglblem5aN
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let vf: setvar f
  let vq: setvar q
  let vs: setvar s
  let vh: setvar h
  let c.le: class .<_
  let cA: class A
  let cP: class P
  let cT: class T
  let cY: class Y
  assume dihglblem5a.b: |- B = ( Base ` K )
  assume dihglblem5a.m: |- ./\ = ( meet ` K )
  assume dihglblem5a.h: |- H = ( LHyp ` K )
  assume dihglblem5a.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. B ) -> ( I ` ( X ./\ W ) ) = ( ( I ` X ) i^i ( I ` W ) ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    cX
    cW
    c.an
    co
    #
    cI
    cfv
    #
    cX
    cI
    cfv
    #
    cW
    cI
    cfv
    #
    cin
    #
    wceq
    #
    @4
    @6
    wa
    #
    @8
    @9
    @11
    @13
    @7
    cX
    cI
    @13
    @6
    @7
    cX
    wceq
    #
    @4
    @6
    simpr
    #
    @13
    cK
    clat
    wcel
    #
    @3
    cW
    cB
    wcel
    #
    @6
    @14
    wb
    @0
    @16
    @1
    @3
    @6
    cK
    hllat
    ad3antrrr
    @2
    @3
    @6
    simplr
    #
    @1
    @17
    @0
    @3
    @6
    cB
    cH
    cK
    cW
    dihglblem5a.b
    dihglblem5a.h
    lhpbase
    ad3antlr
    #
    cB
    cK
    @5
    c.an
    cX
    cW
    dihglblem5a.b
    @5
    eqid
    #
    dihglblem5a.m
    latleeqm1
    syl3anc
    mpbid
    fveq2d
    @13
    @9
    @10
    wss
    #
    @11
    @9
    wceq
    @13
    @21
    @6
    @15
    @13
    @2
    @3
    @17
    @21
    @6
    wb
    @2
    @3
    @6
    simpll
    @18
    @19
    cB
    cH
    cI
    cK
    @5
    cW
    cX
    cW
    dihglblem5a.b
    @20
    dihglblem5a.h
    dihglblem5a.i
    dihord
    syl3anc
    mpbird
    @9
    @10
    df-ss
    sylib
    eqtr4d
    @2
    @3
    @6
    wn
    @12
    cK
    catm
    cfv
    #
    cB
    cW
    cK
    coc
    cfv
    cfv
    #
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cW
    cK
    cltrn
    cfv
    cfv
    #
    vh
    cW
    cK
    ctendo
    cfv
    cfv
    #
    @23
    vh
    cv
    cfv
    vq
    cv
    wceq
    vh
    @25
    crio
    #
    cH
    cI
    cK
    cjn
    cfv
    #
    cK
    @5
    c.an
    cW
    cX
    vh
    @25
    cid
    cB
    cres
    cmpt
    #
    vq
    dihglblem5a.b
    dihglblem5a.m
    dihglblem5a.h
    dihglblem5a.i
    @20
    @28
    eqid
    @22
    eqid
    @23
    eqid
    @25
    eqid
    @24
    eqid
    @26
    eqid
    @27
    eqid
    @29
    eqid
    dihglblem5apreN
    anassrs
    pm2.61dan
end
