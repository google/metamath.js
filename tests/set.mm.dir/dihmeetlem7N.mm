include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "co.mm"
include "cp0.mm"
include "cfv.mm"
include "wceq.mm"
include "simprr.mm"
include "cal.mm"
include "wb.mm"
include "simpl1.mm"
include "hlatl.mm"
include "syl.mm"
include "simprl.mm"
include "simpl3.mm"
include "eqid.mm"
include "atnle.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "oveq2d.mm"
include "clat.mm"
include "hllat.mm"
include "simpl2.mm"
include "latmcl.mm"
include "latmle2.mm"
include "atmod1i2.mm"
include "syl131anc.mm"
include "col.mm"
include "hlol.mm"
include "olj01.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"

theorem dihmeetlem7N
  let cA: class A
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume dihmeetlem7.b: |- B = ( Base ` K )
  assume dihmeetlem7.l: |- .<_ = ( le ` K )
  assume dihmeetlem7.j: |- .\/ = ( join ` K )
  assume dihmeetlem7.m: |- ./\ = ( meet ` K )
  assume dihmeetlem7.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ X e. B /\ Y e. B ) /\ ( p e. A /\ -. p .<_ Y ) ) -> ( ( ( X ./\ Y ) .\/ p ) ./\ Y ) = ( X ./\ Y ) )

  proof
    cK
    chlt
    wcel
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
    @4
    cY
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    cX
    cY
    c.an
    co
    #
    @4
    cY
    c.an
    co
    #
    c.or
    co
    #
    @9
    cK
    cp0
    cfv
    #
    c.or
    co
    #
    @9
    @4
    c.or
    co
    cY
    c.an
    co
    #
    @9
    @8
    @10
    @12
    @9
    c.or
    @8
    @6
    @10
    @12
    wceq
    #
    @3
    @5
    @6
    simprr
    @8
    cK
    cal
    wcel
    #
    @5
    @2
    @6
    @15
    wb
    @8
    @0
    @16
    @0
    @1
    @2
    @7
    simpl1
    #
    cK
    hlatl
    syl
    @3
    @5
    @6
    simprl
    #
    @0
    @1
    @2
    @7
    simpl3
    #
    cA
    cB
    @4
    cK
    c.le
    c.an
    cY
    @12
    dihmeetlem7.b
    dihmeetlem7.l
    dihmeetlem7.m
    @12
    eqid
    #
    dihmeetlem7.a
    atnle
    syl3anc
    mpbid
    oveq2d
    @8
    @0
    @5
    @9
    cB
    wcel
    #
    @2
    @9
    cY
    c.le
    wbr
    #
    @11
    @14
    wceq
    @17
    @18
    @8
    cK
    clat
    wcel
    #
    @1
    @2
    @21
    @8
    @0
    @23
    @17
    cK
    hllat
    syl
    #
    @0
    @1
    @2
    @7
    simpl2
    #
    @19
    cB
    cK
    c.an
    cX
    cY
    dihmeetlem7.b
    dihmeetlem7.m
    latmcl
    syl3anc
    #
    @19
    @8
    @23
    @1
    @2
    @22
    @24
    @25
    @19
    cB
    cK
    c.le
    c.an
    cX
    cY
    dihmeetlem7.b
    dihmeetlem7.l
    dihmeetlem7.m
    latmle2
    syl3anc
    cA
    cB
    @4
    c.or
    cK
    c.le
    c.an
    @9
    cY
    dihmeetlem7.b
    dihmeetlem7.l
    dihmeetlem7.j
    dihmeetlem7.m
    dihmeetlem7.a
    atmod1i2
    syl131anc
    @8
    cK
    col
    wcel
    #
    @21
    @13
    @9
    wceq
    @8
    @0
    @27
    @17
    cK
    hlol
    syl
    @26
    cB
    c.or
    cK
    @9
    @12
    dihmeetlem7.b
    dihmeetlem7.j
    @20
    olj01
    syl2anc
    3eqtr3d
end
