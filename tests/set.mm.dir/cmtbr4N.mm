include "coml.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cmtbr3N.mm"
include "clat.mm"
include "omllat.mm"
include "latmle2.mm"
include "syl3an1.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "wa.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "cops.mm"
include "omlop.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "simp3.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "latmle1.mm"
include "anim1i.mm"
include "ex.mm"
include "wb.mm"
include "latmcl.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "sylibd.mm"
include "latlej2.mm"
include "wi.mm"
include "latmlem2.mm"
include "mpd.mm"
include "jctird.mm"
include "latasymb.mm"
include "impbid.mm"
include "bitrd.mm"

theorem cmtbr4N
  let cB: class B
  let cC: class C
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume cmtbr4.b: |- B = ( Base ` K )
  assume cmtbr4.l: |- .<_ = ( le ` K )
  assume cmtbr4.j: |- .\/ = ( join ` K )
  assume cmtbr4.m: |- ./\ = ( meet ` K )
  assume cmtbr4.o: |- ._|_ = ( oc ` K )
  assume cmtbr4.c: |- C = ( cm ` K )


  assert |- ( ( K e. OML /\ X e. B /\ Y e. B ) -> ( X C Y <-> ( X ./\ ( ( ._|_ ` X ) .\/ Y ) ) .<_ Y ) )

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
    cX
    c.pe
    cfv
    #
    cY
    c.or
    co
    #
    c.an
    co
    #
    cX
    cY
    c.an
    co
    #
    wceq
    #
    @6
    cY
    c.le
    wbr
    #
    cB
    cC
    c.or
    cK
    c.an
    c.pe
    cX
    cY
    cmtbr4.b
    cmtbr4.j
    cmtbr4.m
    cmtbr4.o
    cmtbr4.c
    cmtbr3N
    @3
    @8
    @9
    @3
    @9
    @8
    @7
    cY
    c.le
    wbr
    #
    @0
    cK
    clat
    wcel
    #
    @1
    @2
    @10
    cK
    omllat
    #
    cB
    cK
    c.le
    c.an
    cX
    cY
    cmtbr4.b
    cmtbr4.l
    cmtbr4.m
    latmle2
    syl3an1
    @6
    @7
    cY
    c.le
    breq1
    syl5ibrcom
    @3
    @9
    @6
    @7
    c.le
    wbr
    #
    @7
    @6
    c.le
    wbr
    #
    wa
    #
    @8
    @3
    @9
    @13
    @14
    @3
    @9
    @6
    cX
    c.le
    wbr
    #
    @9
    wa
    #
    @13
    @3
    @9
    @17
    @3
    @16
    @9
    @3
    @11
    @1
    @5
    cB
    wcel
    #
    @16
    @0
    @1
    @11
    @2
    @12
    3ad2ant1
    #
    @0
    @1
    @2
    simp2
    #
    @3
    @11
    @4
    cB
    wcel
    #
    @2
    @18
    @19
    @3
    cK
    cops
    wcel
    #
    @1
    @21
    @0
    @1
    @22
    @2
    cK
    omlop
    3ad2ant1
    @20
    cB
    cK
    c.pe
    cX
    cmtbr4.b
    cmtbr4.o
    opoccl
    syl2anc
    #
    @0
    @1
    @2
    simp3
    #
    cB
    c.or
    cK
    @4
    cY
    cmtbr4.b
    cmtbr4.j
    latjcl
    syl3anc
    #
    cB
    cK
    c.le
    c.an
    cX
    @5
    cmtbr4.b
    cmtbr4.l
    cmtbr4.m
    latmle1
    syl3anc
    anim1i
    ex
    @3
    @11
    @6
    cB
    wcel
    #
    @1
    @2
    @17
    @13
    wb
    @19
    @3
    @11
    @1
    @18
    @26
    @19
    @20
    @25
    cB
    cK
    c.an
    cX
    @5
    cmtbr4.b
    cmtbr4.m
    latmcl
    syl3anc
    #
    @20
    @24
    cB
    cK
    c.le
    c.an
    @6
    cX
    cY
    cmtbr4.b
    cmtbr4.l
    cmtbr4.m
    latlem12
    syl13anc
    sylibd
    @3
    cY
    @5
    c.le
    wbr
    #
    @14
    @3
    @11
    @21
    @2
    @28
    @19
    @23
    @24
    cB
    c.or
    cK
    c.le
    @4
    cY
    cmtbr4.b
    cmtbr4.l
    cmtbr4.j
    latlej2
    syl3anc
    @3
    @11
    @2
    @18
    @1
    @28
    @14
    wi
    @19
    @24
    @25
    @20
    cB
    cK
    c.le
    c.an
    cY
    @5
    cX
    cmtbr4.b
    cmtbr4.l
    cmtbr4.m
    latmlem2
    syl13anc
    mpd
    jctird
    @3
    @11
    @26
    @7
    cB
    wcel
    #
    @15
    @8
    wb
    @19
    @27
    @0
    @11
    @1
    @2
    @29
    @12
    cB
    cK
    c.an
    cX
    cY
    cmtbr4.b
    cmtbr4.m
    latmcl
    syl3an1
    cB
    cK
    c.le
    @6
    @7
    cmtbr4.b
    cmtbr4.l
    latasymb
    syl3anc
    sylibd
    impbid
    bitrd
end
