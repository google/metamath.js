include "coml.mm"
include "wcel.mm"
include "w3a.mm"
include "cmee.mm"
include "cfv.mm"
include "co.mm"
include "cjn.mm"
include "wceq.mm"
include "wbr.mm"
include "clat.mm"
include "omllat.mm"
include "3ad2ant1.mm"
include "eqid.mm"
include "latmcl.mm"
include "syl3an1.mm"
include "simp2.mm"
include "cops.mm"
include "omlop.mm"
include "simp3.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "syl3anc.mm"
include "latjcom.mm"
include "opococ.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "eqeq2d.mm"
include "cmtvalN.mm"
include "wb.mm"
include "syld3an3.mm"
include "3bitr4d.mm"

theorem cmt2N
  let cB: class B
  let cC: class C
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume cmt2.b: |- B = ( Base ` K )
  assume cmt2.o: |- ._|_ = ( oc ` K )
  assume cmt2.c: |- C = ( cm ` K )


  assert |- ( ( K e. OML /\ X e. B /\ Y e. B ) -> ( X C Y <-> X C ( ._|_ ` Y ) ) )

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
    cX
    cY
    cK
    cmee
    cfv
    #
    co
    #
    cX
    cY
    c.pe
    cfv
    #
    @4
    co
    #
    cK
    cjn
    cfv
    #
    co
    #
    wceq
    cX
    @7
    cX
    @6
    c.pe
    cfv
    #
    @4
    co
    #
    @8
    co
    #
    wceq
    #
    cX
    cY
    cC
    wbr
    cX
    @6
    cC
    wbr
    #
    @3
    @9
    @12
    cX
    @3
    @9
    @7
    @5
    @8
    co
    #
    @12
    @3
    cK
    clat
    wcel
    #
    @5
    cB
    wcel
    #
    @7
    cB
    wcel
    #
    @9
    @15
    wceq
    @0
    @1
    @16
    @2
    cK
    omllat
    #
    3ad2ant1
    #
    @0
    @16
    @1
    @2
    @17
    @19
    cB
    cK
    @4
    cX
    cY
    cmt2.b
    @4
    eqid
    #
    latmcl
    syl3an1
    @3
    @16
    @1
    @6
    cB
    wcel
    #
    @18
    @20
    @0
    @1
    @2
    simp2
    @3
    cK
    cops
    wcel
    #
    @2
    @22
    @0
    @1
    @23
    @2
    cK
    omlop
    3ad2ant1
    #
    @0
    @1
    @2
    simp3
    #
    cB
    cK
    c.pe
    cY
    cmt2.b
    cmt2.o
    opoccl
    syl2anc
    #
    cB
    cK
    @4
    cX
    @6
    cmt2.b
    @21
    latmcl
    syl3anc
    cB
    @8
    cK
    @5
    @7
    cmt2.b
    @8
    eqid
    #
    latjcom
    syl3anc
    @3
    @11
    @5
    @7
    @8
    @3
    @10
    cY
    cX
    @4
    @3
    @23
    @2
    @10
    cY
    wceq
    @24
    @25
    cB
    cK
    c.pe
    cY
    cmt2.b
    cmt2.o
    opococ
    syl2anc
    oveq2d
    oveq2d
    eqtr4d
    eqeq2d
    coml
    cB
    cC
    @8
    cK
    @4
    c.pe
    cX
    cY
    cmt2.b
    @27
    @21
    cmt2.o
    cmt2.c
    cmtvalN
    @0
    @1
    @2
    @22
    @14
    @13
    wb
    @26
    coml
    cB
    cC
    @8
    cK
    @4
    c.pe
    cX
    @6
    cmt2.b
    @27
    @21
    cmt2.o
    cmt2.c
    cmtvalN
    syld3an3
    3bitr4d
end
