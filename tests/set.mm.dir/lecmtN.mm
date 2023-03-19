include "coml.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "coc.mm"
include "cfv.mm"
include "cjn.mm"
include "co.mm"
include "cmee.mm"
include "clat.mm"
include "omllat.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "cops.mm"
include "omlop.mm"
include "eqid.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "simp3.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "latmle1.mm"
include "wa.mm"
include "wi.mm"
include "latmcl.mm"
include "lattr.mm"
include "syl13anc.mm"
include "mpand.mm"
include "cmtbr4N.mm"
include "sylibrd.mm"

theorem lecmtN
  let cB: class B
  let cC: class C
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  assume lecmt.b: |- B = ( Base ` K )
  assume lecmt.l: |- .<_ = ( le ` K )
  assume lecmt.c: |- C = ( cm ` K )


  assert |- ( ( K e. OML /\ X e. B /\ Y e. B ) -> ( X .<_ Y -> X C Y ) )

  proof
    cK
    coml
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
    cX
    cY
    c.le
    wbr
    #
    cX
    cX
    cK
    coc
    cfv
    #
    cfv
    #
    cY
    cK
    cjn
    cfv
    #
    co
    #
    cK
    cmee
    cfv
    #
    co
    #
    cY
    c.le
    wbr
    #
    cX
    cY
    cC
    wbr
    @3
    @10
    cX
    c.le
    wbr
    #
    @4
    @11
    @3
    cK
    clat
    wcel
    #
    @1
    @8
    cB
    wcel
    #
    @12
    @0
    @1
    @13
    @2
    cK
    omllat
    3ad2ant1
    #
    @0
    @1
    @2
    simp2
    #
    @3
    @13
    @6
    cB
    wcel
    #
    @2
    @14
    @15
    @3
    cK
    cops
    wcel
    #
    @1
    @17
    @0
    @1
    @18
    @2
    cK
    omlop
    3ad2ant1
    @16
    cB
    cK
    @5
    cX
    lecmt.b
    @5
    eqid
    #
    opoccl
    syl2anc
    @0
    @1
    @2
    simp3
    #
    cB
    @7
    cK
    @6
    cY
    lecmt.b
    @7
    eqid
    #
    latjcl
    syl3anc
    #
    cB
    cK
    c.le
    @9
    cX
    @8
    lecmt.b
    lecmt.l
    @9
    eqid
    #
    latmle1
    syl3anc
    @3
    @13
    @10
    cB
    wcel
    #
    @1
    @2
    @12
    @4
    wa
    @11
    wi
    @15
    @3
    @13
    @1
    @14
    @24
    @15
    @16
    @22
    cB
    cK
    @9
    cX
    @8
    lecmt.b
    @23
    latmcl
    syl3anc
    @16
    @20
    cB
    cK
    c.le
    @10
    cX
    cY
    lecmt.b
    lecmt.l
    lattr
    syl13anc
    mpand
    cB
    cC
    @7
    cK
    c.le
    @9
    @5
    cX
    cY
    lecmt.b
    lecmt.l
    @21
    @23
    @19
    lecmt.c
    cmtbr4N
    sylibrd
end
