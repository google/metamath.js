include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "w3a.mm"
include "co.mm"
include "clat.mm"
include "wceq.mm"
include "simpl1l.mm"
include "hllat.mm"
include "syl.mm"
include "simpl3l.mm"
include "atbase.mm"
include "simpr1.mm"
include "latmcom.mm"
include "syl3anc.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr2.mm"
include "simpr3.mm"
include "lhpmcvr4N.mm"
include "syl123anc.mm"
include "cal.mm"
include "wb.mm"
include "hlatl.mm"
include "atnle.mm"
include "mpbid.mm"
include "eqtr3d.mm"

theorem dihmeetlem17N
  let cA: class A
  let cB: class B
  let c.po: class .(+)
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vp: setvar p
  let vh: setvar h
  let vr: setvar r
  assume dihmeetlem14.b: |- B = ( Base ` K )
  assume dihmeetlem14.l: |- .<_ = ( le ` K )
  assume dihmeetlem14.h: |- H = ( LHyp ` K )
  assume dihmeetlem14.j: |- .\/ = ( join ` K )
  assume dihmeetlem14.m: |- ./\ = ( meet ` K )
  assume dihmeetlem14.a: |- A = ( Atoms ` K )
  assume dihmeetlem14.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihmeetlem14.s: |- .(+) = ( LSSum ` U )
  assume dihmeetlem14.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihmeetlem17.o: |- .0. = ( 0. ` K )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) /\ ( p e. A /\ -. p .<_ W ) ) /\ ( Y e. B /\ ( X ./\ Y ) .<_ W /\ p .<_ X ) ) -> ( Y ./\ p ) = .0. )

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
    cX
    cW
    c.le
    wbr
    wn
    wa
    #
    vp
    cv
    #
    cA
    wcel
    #
    @4
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cY
    cB
    wcel
    #
    cX
    cY
    c.an
    co
    cW
    c.le
    wbr
    #
    @4
    cX
    c.le
    wbr
    #
    w3a
    #
    wa
    #
    @4
    cY
    c.an
    co
    #
    cY
    @4
    c.an
    co
    #
    c.0
    @13
    cK
    clat
    wcel
    #
    @4
    cB
    wcel
    #
    @9
    @14
    @15
    wceq
    @13
    @0
    @16
    @0
    @1
    @3
    @7
    @12
    simpl1l
    #
    cK
    hllat
    syl
    @13
    @5
    @17
    @5
    @6
    @2
    @3
    @12
    simpl3l
    #
    cA
    cB
    @4
    cK
    dihmeetlem14.b
    dihmeetlem14.a
    atbase
    syl
    @8
    @9
    @10
    @11
    simpr1
    #
    cB
    cK
    c.an
    @4
    cY
    dihmeetlem14.b
    dihmeetlem14.m
    latmcom
    syl3anc
    @13
    @4
    cY
    c.le
    wbr
    wn
    #
    @14
    c.0
    wceq
    #
    @13
    @2
    @3
    @7
    @9
    @10
    @11
    @21
    @2
    @3
    @7
    @12
    simpl1
    @2
    @3
    @7
    @12
    simpl2
    @2
    @3
    @7
    @12
    simpl3
    @20
    @8
    @9
    @10
    @11
    simpr2
    @8
    @9
    @10
    @11
    simpr3
    cA
    cB
    @4
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    cY
    dihmeetlem14.b
    dihmeetlem14.l
    dihmeetlem14.j
    dihmeetlem14.m
    dihmeetlem14.a
    dihmeetlem14.h
    lhpmcvr4N
    syl123anc
    @13
    cK
    cal
    wcel
    #
    @5
    @9
    @21
    @22
    wb
    @13
    @0
    @23
    @18
    cK
    hlatl
    syl
    @19
    @20
    cA
    cB
    @4
    cK
    c.le
    c.an
    cY
    c.0
    dihmeetlem14.b
    dihmeetlem14.l
    dihmeetlem14.m
    dihmeetlem17.o
    dihmeetlem14.a
    atnle
    syl3anc
    mpbid
    eqtr3d
end
