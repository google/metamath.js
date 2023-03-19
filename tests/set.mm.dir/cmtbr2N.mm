include "coml.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cmt4N.mm"
include "wb.mm"
include "simp1.mm"
include "cops.mm"
include "omlop.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "simp3.mm"
include "cmtvalN.mm"
include "syl3anc.mm"
include "eqcom.mm"
include "a1i.mm"
include "clat.mm"
include "omllat.mm"
include "latjcl.mm"
include "syl3an1.mm"
include "latmcl.mm"
include "opcon3b.mm"
include "col.mm"
include "omlol.mm"
include "oldmm1.mm"
include "oldmj1.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "eqeq2d.mm"
include "3bitrrd.mm"
include "3bitrd.mm"

theorem cmtbr2N
  let cB: class B
  let cC: class C
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume cmtbr2.b: |- B = ( Base ` K )
  assume cmtbr2.j: |- .\/ = ( join ` K )
  assume cmtbr2.m: |- ./\ = ( meet ` K )
  assume cmtbr2.o: |- ._|_ = ( oc ` K )
  assume cmtbr2.c: |- C = ( cm ` K )


  assert |- ( ( K e. OML /\ X e. B /\ Y e. B ) -> ( X C Y <-> X = ( ( X .\/ Y ) ./\ ( X .\/ ( ._|_ ` Y ) ) ) ) )

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
    cC
    wbr
    cX
    c.pe
    cfv
    #
    cY
    c.pe
    cfv
    #
    cC
    wbr
    #
    @4
    @4
    @5
    c.an
    co
    #
    @4
    @5
    c.pe
    cfv
    c.an
    co
    #
    c.or
    co
    #
    wceq
    #
    cX
    cX
    cY
    c.or
    co
    #
    cX
    @5
    c.or
    co
    #
    c.an
    co
    #
    wceq
    #
    cB
    cC
    cK
    c.pe
    cX
    cY
    cmtbr2.b
    cmtbr2.o
    cmtbr2.c
    cmt4N
    @3
    @0
    @4
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    @6
    @10
    wb
    @0
    @1
    @2
    simp1
    @3
    cK
    cops
    wcel
    #
    @1
    @15
    @0
    @1
    @17
    @2
    cK
    omlop
    3ad2ant1
    #
    @0
    @1
    @2
    simp2
    #
    cB
    cK
    c.pe
    cX
    cmtbr2.b
    cmtbr2.o
    opoccl
    syl2anc
    @3
    @17
    @2
    @16
    @18
    @0
    @1
    @2
    simp3
    cB
    cK
    c.pe
    cY
    cmtbr2.b
    cmtbr2.o
    opoccl
    syl2anc
    #
    coml
    cB
    cC
    c.or
    cK
    c.an
    c.pe
    @4
    @5
    cmtbr2.b
    cmtbr2.j
    cmtbr2.m
    cmtbr2.o
    cmtbr2.c
    cmtvalN
    syl3anc
    @3
    @14
    @13
    cX
    wceq
    #
    @4
    @13
    c.pe
    cfv
    #
    wceq
    #
    @10
    @14
    @21
    wb
    @3
    cX
    @13
    eqcom
    a1i
    @3
    @17
    @13
    cB
    wcel
    #
    @1
    @21
    @23
    wb
    @18
    @3
    cK
    clat
    wcel
    #
    @11
    cB
    wcel
    #
    @12
    cB
    wcel
    #
    @24
    @0
    @1
    @25
    @2
    cK
    omllat
    #
    3ad2ant1
    #
    @0
    @25
    @1
    @2
    @26
    @28
    cB
    c.or
    cK
    cX
    cY
    cmtbr2.b
    cmtbr2.j
    latjcl
    syl3an1
    #
    @3
    @25
    @1
    @16
    @27
    @29
    @19
    @20
    cB
    c.or
    cK
    cX
    @5
    cmtbr2.b
    cmtbr2.j
    latjcl
    syl3anc
    #
    cB
    cK
    c.an
    @11
    @12
    cmtbr2.b
    cmtbr2.m
    latmcl
    syl3anc
    @19
    cB
    cK
    c.pe
    @13
    cX
    cmtbr2.b
    cmtbr2.o
    opcon3b
    syl3anc
    @3
    @22
    @9
    @4
    @3
    @22
    @11
    c.pe
    cfv
    #
    @12
    c.pe
    cfv
    #
    c.or
    co
    #
    @9
    @3
    cK
    col
    wcel
    #
    @26
    @27
    @22
    @34
    wceq
    @0
    @1
    @35
    @2
    cK
    omlol
    #
    3ad2ant1
    #
    @30
    @31
    cB
    c.or
    cK
    c.an
    c.pe
    @11
    @12
    cmtbr2.b
    cmtbr2.j
    cmtbr2.m
    cmtbr2.o
    oldmm1
    syl3anc
    @3
    @32
    @7
    @33
    @8
    c.or
    @0
    @35
    @1
    @2
    @32
    @7
    wceq
    @36
    cB
    c.or
    cK
    c.an
    c.pe
    cX
    cY
    cmtbr2.b
    cmtbr2.j
    cmtbr2.m
    cmtbr2.o
    oldmj1
    syl3an1
    @3
    @35
    @1
    @16
    @33
    @8
    wceq
    @37
    @19
    @20
    cB
    c.or
    cK
    c.an
    c.pe
    cX
    @5
    cmtbr2.b
    cmtbr2.j
    cmtbr2.m
    cmtbr2.o
    oldmj1
    syl3anc
    oveq12d
    eqtrd
    eqeq2d
    3bitrrd
    3bitrd
end
