include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "cp0.mm"
include "cin.mm"
include "csn.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr1.mm"
include "simpl3.mm"
include "simpr33.mm"
include "simpr31.mm"
include "eqid.mm"
include "dihmeetlem17N.mm"
include "syl33anc.mm"
include "fveq2d.mm"
include "simpr2.mm"
include "simpr32.mm"
include "cops.mm"
include "simpl1l.mm"
include "hlop.mm"
include "syl.mm"
include "simpl1r.mm"
include "lhpbase.mm"
include "op0le.mm"
include "syl2anc.mm"
include "eqbrtrd.mm"
include "dihmeetlem16N.mm"
include "dih0.mm"
include "3eqtr3d.mm"

theorem dihmeetlem18N
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
  let vr: setvar r
  let vp: setvar p
  let vh: setvar h
  assume dihmeetlem14.b: |- B = ( Base ` K )
  assume dihmeetlem14.l: |- .<_ = ( le ` K )
  assume dihmeetlem14.h: |- H = ( LHyp ` K )
  assume dihmeetlem14.j: |- .\/ = ( join ` K )
  assume dihmeetlem14.m: |- ./\ = ( meet ` K )
  assume dihmeetlem14.a: |- A = ( Atoms ` K )
  assume dihmeetlem14.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihmeetlem14.s: |- .(+) = ( LSSum ` U )
  assume dihmeetlem14.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihmeetlem18.z: |- .0. = ( 0g ` U )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) /\ Y e. B ) /\ ( ( p e. A /\ -. p .<_ W ) /\ ( r e. A /\ -. r .<_ W ) /\ ( p .<_ X /\ r .<_ Y /\ ( X ./\ Y ) .<_ W ) ) ) -> ( ( I ` Y ) i^i ( I ` p ) ) = { .0. } )

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
    cY
    cB
    wcel
    #
    w3a
    #
    vp
    cv
    #
    cA
    wcel
    @6
    cW
    c.le
    wbr
    wn
    wa
    #
    vr
    cv
    #
    cA
    wcel
    @8
    cW
    c.le
    wbr
    wn
    wa
    #
    @6
    cX
    c.le
    wbr
    #
    @8
    cY
    c.le
    wbr
    #
    cX
    cY
    c.an
    co
    cW
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    wa
    #
    cY
    @6
    c.an
    co
    #
    cI
    cfv
    #
    cK
    cp0
    cfv
    #
    cI
    cfv
    #
    cY
    cI
    cfv
    @6
    cI
    cfv
    cin
    #
    c.0
    csn
    #
    @15
    @16
    @18
    cI
    @15
    @2
    @3
    @7
    @4
    @12
    @10
    @16
    @18
    wceq
    @2
    @3
    @4
    @14
    simpl1
    #
    @2
    @3
    @4
    @14
    simpl2
    @5
    @7
    @9
    @13
    simpr1
    #
    @2
    @3
    @4
    @14
    simpl3
    #
    @10
    @11
    @12
    @7
    @9
    @5
    simpr33
    @10
    @11
    @12
    @7
    @9
    @5
    simpr31
    cA
    cB
    c.po
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cW
    cX
    cY
    @18
    vp
    dihmeetlem14.b
    dihmeetlem14.l
    dihmeetlem14.h
    dihmeetlem14.j
    dihmeetlem14.m
    dihmeetlem14.a
    dihmeetlem14.u
    dihmeetlem14.s
    dihmeetlem14.i
    @18
    eqid
    #
    dihmeetlem17N
    syl33anc
    #
    fveq2d
    @15
    @2
    @4
    @7
    @9
    @11
    @16
    cW
    c.le
    wbr
    @17
    @20
    wceq
    @22
    @24
    @23
    @5
    @7
    @9
    @13
    simpr2
    @10
    @11
    @12
    @7
    @9
    @5
    simpr32
    @15
    @16
    @18
    cW
    c.le
    @26
    @15
    cK
    cops
    wcel
    #
    cW
    cB
    wcel
    #
    @18
    cW
    c.le
    wbr
    @15
    @0
    @27
    @0
    @1
    @3
    @4
    @14
    simpl1l
    cK
    hlop
    syl
    @15
    @1
    @28
    @0
    @1
    @3
    @4
    @14
    simpl1r
    cB
    cH
    cK
    cW
    dihmeetlem14.b
    dihmeetlem14.h
    lhpbase
    syl
    cB
    cK
    c.le
    cW
    @18
    dihmeetlem14.b
    dihmeetlem14.l
    @25
    op0le
    syl2anc
    eqbrtrd
    cA
    cB
    c.po
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cW
    cY
    vr
    vp
    dihmeetlem14.b
    dihmeetlem14.l
    dihmeetlem14.h
    dihmeetlem14.j
    dihmeetlem14.m
    dihmeetlem14.a
    dihmeetlem14.u
    dihmeetlem14.s
    dihmeetlem14.i
    dihmeetlem16N
    syl33anc
    @15
    @2
    @19
    @21
    wceq
    @22
    cU
    cH
    cI
    cK
    c.0
    cW
    @18
    @25
    dihmeetlem14.h
    dihmeetlem14.i
    dihmeetlem14.u
    dihmeetlem18.z
    dih0
    syl
    3eqtr3d
end
