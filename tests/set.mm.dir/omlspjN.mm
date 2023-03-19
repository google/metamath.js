include "coml.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cp0.mm"
include "clat.mm"
include "wceq.mm"
include "omllat.mm"
include "3ad2ant1.mm"
include "cops.mm"
include "omlop.mm"
include "simp2r.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "latmcom.mm"
include "syl3anc.mm"
include "eqid.mm"
include "opnoncon.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "ccmtN.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp3.mm"
include "cmtidN.mm"
include "wb.mm"
include "cmt3N.mm"
include "mpbid.mm"
include "omlmod1i2N.mm"
include "syl132anc.mm"
include "col.mm"
include "omlol.mm"
include "olj01.mm"
include "3eqtr3d.mm"

theorem omlspjN
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume omlspj.b: |- B = ( Base ` K )
  assume omlspj.l: |- .<_ = ( le ` K )
  assume omlspj.j: |- .\/ = ( join ` K )
  assume omlspj.m: |- ./\ = ( meet ` K )
  assume omlspj.o: |- ._|_ = ( oc ` K )


  assert |- ( ( K e. OML /\ ( X e. B /\ Y e. B ) /\ X .<_ Y ) -> ( ( X .\/ ( ._|_ ` Y ) ) ./\ Y ) = X )

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
    wa
    #
    cX
    cY
    c.le
    wbr
    #
    w3a
    #
    cX
    cY
    c.pe
    cfv
    #
    cY
    c.an
    co
    #
    c.or
    co
    #
    cX
    cK
    cp0
    cfv
    #
    c.or
    co
    #
    cX
    @6
    c.or
    co
    cY
    c.an
    co
    #
    cX
    @5
    @7
    @9
    cX
    c.or
    @5
    @7
    cY
    @6
    c.an
    co
    #
    @9
    @5
    cK
    clat
    wcel
    #
    @6
    cB
    wcel
    #
    @2
    @7
    @12
    wceq
    @0
    @3
    @13
    @4
    cK
    omllat
    3ad2ant1
    @5
    cK
    cops
    wcel
    #
    @2
    @14
    @0
    @3
    @15
    @4
    cK
    omlop
    3ad2ant1
    #
    @0
    @1
    @2
    @4
    simp2r
    #
    cB
    cK
    c.pe
    cY
    omlspj.b
    omlspj.o
    opoccl
    syl2anc
    #
    @17
    cB
    cK
    c.an
    @6
    cY
    omlspj.b
    omlspj.m
    latmcom
    syl3anc
    @5
    @15
    @2
    @12
    @9
    wceq
    @16
    @17
    cB
    cK
    c.an
    c.pe
    cY
    @9
    omlspj.b
    omlspj.o
    omlspj.m
    @9
    eqid
    #
    opnoncon
    syl2anc
    eqtrd
    oveq2d
    @5
    @0
    @1
    @14
    @2
    @4
    @6
    cY
    cK
    ccmtN
    cfv
    #
    wbr
    #
    @8
    @11
    wceq
    @0
    @3
    @4
    simp1
    #
    @0
    @1
    @2
    @4
    simp2l
    #
    @18
    @17
    @0
    @3
    @4
    simp3
    @5
    cY
    cY
    @20
    wbr
    #
    @21
    @5
    @0
    @2
    @24
    @22
    @17
    cB
    @20
    cK
    cY
    omlspj.b
    @20
    eqid
    #
    cmtidN
    syl2anc
    @5
    @0
    @2
    @2
    @24
    @21
    wb
    @22
    @17
    @17
    cB
    @20
    cK
    c.pe
    cY
    cY
    omlspj.b
    omlspj.o
    @25
    cmt3N
    syl3anc
    mpbid
    cB
    @20
    c.or
    cK
    c.le
    c.an
    cX
    @6
    cY
    omlspj.b
    omlspj.l
    omlspj.j
    omlspj.m
    @25
    omlmod1i2N
    syl132anc
    @5
    cK
    col
    wcel
    #
    @1
    @10
    cX
    wceq
    @0
    @3
    @26
    @4
    cK
    omlol
    3ad2ant1
    @23
    cB
    c.or
    cK
    cX
    @9
    omlspj.b
    omlspj.j
    @19
    olj01
    syl2anc
    3eqtr3d
end
