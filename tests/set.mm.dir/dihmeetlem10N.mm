include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "cfv.mm"
include "cin.mm"
include "wceq.mm"
include "simpl1l.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simprll.mm"
include "simprr.mm"
include "dihmeetlem5.mm"
include "syl32anc.mm"
include "fveq2d.mm"
include "simpl1.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "dihmeetlem6.mm"
include "dihmeetcN.mm"
include "syl121anc.mm"
include "eqtr3d.mm"

theorem dihmeetlem10N
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
  let vp: setvar p
  assume dihmeetlem9.b: |- B = ( Base ` K )
  assume dihmeetlem9.l: |- .<_ = ( le ` K )
  assume dihmeetlem9.h: |- H = ( LHyp ` K )
  assume dihmeetlem9.j: |- .\/ = ( join ` K )
  assume dihmeetlem9.m: |- ./\ = ( meet ` K )
  assume dihmeetlem9.a: |- A = ( Atoms ` K )
  assume dihmeetlem9.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihmeetlem9.s: |- .(+) = ( LSSum ` U )
  assume dihmeetlem9.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ X e. B /\ Y e. B ) /\ ( ( p e. A /\ -. p .<_ W ) /\ p .<_ X ) ) -> ( I ` ( ( X ./\ Y ) .\/ p ) ) = ( ( I ` X ) i^i ( I ` ( Y .\/ p ) ) ) )

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
    #
    @6
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    @6
    cX
    c.le
    wbr
    #
    wa
    #
    wa
    #
    cX
    cY
    @6
    c.or
    co
    #
    c.an
    co
    #
    cI
    cfv
    #
    cX
    cY
    c.an
    co
    @6
    c.or
    co
    #
    cI
    cfv
    cX
    cI
    cfv
    @13
    cI
    cfv
    cin
    #
    @12
    @14
    @16
    cI
    @12
    @0
    @3
    @4
    @7
    @10
    @14
    @16
    wceq
    @0
    @1
    @3
    @4
    @11
    simpl1l
    #
    @2
    @3
    @4
    @11
    simpl2
    #
    @2
    @3
    @4
    @11
    simpl3
    #
    @5
    @7
    @8
    @10
    simprll
    #
    @5
    @9
    @10
    simprr
    cA
    cB
    @6
    c.or
    cK
    c.le
    c.an
    cX
    cY
    dihmeetlem9.b
    dihmeetlem9.l
    dihmeetlem9.j
    dihmeetlem9.m
    dihmeetlem9.a
    dihmeetlem5
    syl32anc
    fveq2d
    @12
    @2
    @3
    @13
    cB
    wcel
    #
    @14
    cW
    c.le
    wbr
    wn
    @15
    @17
    wceq
    @2
    @3
    @4
    @11
    simpl1
    @19
    @12
    cK
    clat
    wcel
    #
    @4
    @6
    cB
    wcel
    #
    @22
    @12
    @0
    @23
    @18
    cK
    hllat
    syl
    @20
    @12
    @7
    @24
    @21
    cA
    cB
    @6
    cK
    dihmeetlem9.b
    dihmeetlem9.a
    atbase
    syl
    cB
    c.or
    cK
    cY
    @6
    dihmeetlem9.b
    dihmeetlem9.j
    latjcl
    syl3anc
    cA
    cB
    @6
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    cY
    dihmeetlem9.b
    dihmeetlem9.l
    dihmeetlem9.h
    dihmeetlem9.j
    dihmeetlem9.m
    dihmeetlem9.a
    dihmeetlem6
    cB
    cH
    cI
    cK
    c.le
    c.an
    cW
    cX
    @13
    dihmeetlem9.b
    dihmeetlem9.l
    dihmeetlem9.m
    dihmeetlem9.h
    dihmeetlem9.i
    dihmeetcN
    syl121anc
    eqtr3d
end
