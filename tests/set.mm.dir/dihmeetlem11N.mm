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
include "dihmeetlem10N.mm"
include "ineq1d.mm"
include "inass.mm"
include "wss.mm"
include "wceq.mm"
include "clat.mm"
include "simpl1l.mm"
include "hllat.mm"
include "syl.mm"
include "simpl3.mm"
include "simprll.mm"
include "atbase.mm"
include "latlej1.mm"
include "syl3anc.mm"
include "wb.mm"
include "simpl1.mm"
include "latjcl.mm"
include "dihord.mm"
include "mpbird.mm"
include "sseqin2.mm"
include "sylib.mm"
include "ineq2d.mm"
include "syl5eq.mm"
include "eqtrd.mm"

theorem dihmeetlem11N
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ X e. B /\ Y e. B ) /\ ( ( p e. A /\ -. p .<_ W ) /\ p .<_ X ) ) -> ( ( I ` ( ( X ./\ Y ) .\/ p ) ) i^i ( I ` Y ) ) = ( ( I ` X ) i^i ( I ` Y ) ) )

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
    c.an
    co
    @6
    c.or
    co
    cI
    cfv
    #
    cY
    cI
    cfv
    #
    cin
    cX
    cI
    cfv
    #
    cY
    @6
    c.or
    co
    #
    cI
    cfv
    #
    cin
    #
    @13
    cin
    #
    @14
    @13
    cin
    #
    @11
    @12
    @17
    @13
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
    vp
    dihmeetlem9.b
    dihmeetlem9.l
    dihmeetlem9.h
    dihmeetlem9.j
    dihmeetlem9.m
    dihmeetlem9.a
    dihmeetlem9.u
    dihmeetlem9.s
    dihmeetlem9.i
    dihmeetlem10N
    ineq1d
    @11
    @18
    @14
    @16
    @13
    cin
    #
    cin
    @19
    @14
    @16
    @13
    inass
    @11
    @20
    @13
    @14
    @11
    @13
    @16
    wss
    #
    @20
    @13
    wceq
    @11
    @21
    cY
    @15
    c.le
    wbr
    #
    @11
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
    @11
    @0
    @23
    @0
    @1
    @3
    @4
    @10
    simpl1l
    cK
    hllat
    syl
    #
    @2
    @3
    @4
    @10
    simpl3
    #
    @11
    @7
    @24
    @5
    @7
    @8
    @9
    simprll
    cA
    cB
    @6
    cK
    dihmeetlem9.b
    dihmeetlem9.a
    atbase
    syl
    #
    cB
    c.or
    cK
    c.le
    cY
    @6
    dihmeetlem9.b
    dihmeetlem9.l
    dihmeetlem9.j
    latlej1
    syl3anc
    @11
    @2
    @4
    @15
    cB
    wcel
    #
    @21
    @22
    wb
    @2
    @3
    @4
    @10
    simpl1
    @26
    @11
    @23
    @4
    @24
    @28
    @25
    @26
    @27
    cB
    c.or
    cK
    cY
    @6
    dihmeetlem9.b
    dihmeetlem9.j
    latjcl
    syl3anc
    cB
    cH
    cI
    cK
    c.le
    cW
    cY
    @15
    dihmeetlem9.b
    dihmeetlem9.l
    dihmeetlem9.h
    dihmeetlem9.i
    dihord
    syl3anc
    mpbird
    @13
    @16
    sseqin2
    sylib
    ineq2d
    syl5eq
    eqtrd
end
