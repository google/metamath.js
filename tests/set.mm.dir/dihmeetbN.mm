include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cin.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "simpl3.mm"
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
include "eqid.mm"
include "dihmeetlem2N.mm"
include "syl121anc.mm"
include "wn.mm"
include "dihmeetlem1N.mm"
include "pm2.61dan.mm"

theorem dihmeetbN
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vq: setvar q
  let vx: setvar x
  assume dihmeetc.b: |- B = ( Base ` K )
  assume dihmeetc.l: |- .<_ = ( le ` K )
  assume dihmeetc.m: |- ./\ = ( meet ` K )
  assume dihmeetc.h: |- H = ( LHyp ` K )
  assume dihmeetc.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. B /\ ( Y e. B /\ Y .<_ W ) ) -> ( I ` ( X ./\ Y ) ) = ( ( I ` X ) i^i ( I ` Y ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    cY
    cW
    c.le
    wbr
    wa
    #
    w3a
    #
    cX
    cW
    c.le
    wbr
    #
    cX
    cY
    c.an
    co
    cI
    cfv
    cX
    cI
    cfv
    cY
    cI
    cfv
    cin
    wceq
    #
    @3
    @4
    wa
    @0
    @1
    @4
    @2
    @5
    @0
    @1
    @2
    @4
    simpl1
    @0
    @1
    @2
    @4
    simpl2
    @3
    @4
    simpr
    @0
    @1
    @2
    @4
    simpl3
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
    vg
    cW
    cK
    ctendo
    cfv
    cfv
    #
    @7
    vg
    cv
    cfv
    vq
    cv
    wceq
    vg
    @9
    crio
    #
    cH
    cI
    cK
    cjn
    cfv
    #
    cK
    c.le
    c.an
    cW
    cX
    cY
    vg
    @9
    cid
    cB
    cres
    cmpt
    #
    vq
    dihmeetc.b
    dihmeetc.m
    dihmeetc.h
    dihmeetc.i
    dihmeetc.l
    @12
    eqid
    #
    @6
    eqid
    #
    @7
    eqid
    #
    @9
    eqid
    #
    @8
    eqid
    #
    @10
    eqid
    #
    @11
    eqid
    #
    @13
    eqid
    #
    dihmeetlem2N
    syl121anc
    @3
    @4
    wn
    #
    wa
    @0
    @1
    @22
    @2
    @5
    @0
    @1
    @2
    @22
    simpl1
    @0
    @1
    @2
    @22
    simpl2
    @3
    @22
    simpr
    @0
    @1
    @2
    @22
    simpl3
    @6
    cB
    @7
    @8
    @9
    vg
    @10
    @11
    cH
    cI
    @12
    cK
    c.le
    c.an
    cW
    cX
    cY
    @13
    vq
    dihmeetc.b
    dihmeetc.m
    dihmeetc.h
    dihmeetc.i
    dihmeetc.l
    @14
    @15
    @16
    @17
    @18
    @19
    @20
    @21
    dihmeetlem1N
    syl121anc
    pm2.61dan
end
