include "col.mm"
include "wcel.mm"
include "w3a.mm"
include "cple.mm"
include "cfv.mm"
include "co.mm"
include "eqid.mm"
include "clat.mm"
include "ollat.mm"
include "3ad2ant1.mm"
include "cops.mm"
include "olop.mm"
include "latmcl.mm"
include "syl3an1.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "sylan.mm"
include "3adant3.mm"
include "3adant2.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "wbr.mm"
include "latlej1.mm"
include "wb.mm"
include "simp2.mm"
include "oplecon1b.mm"
include "mpbid.mm"
include "latlej2.mm"
include "simp3.mm"
include "wa.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "latmle1.mm"
include "oplecon3b.mm"
include "latmle2.mm"
include "latjle12.mm"
include "latasymd.mm"

theorem oldmm1
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume oldmm1.b: |- B = ( Base ` K )
  assume oldmm1.j: |- .\/ = ( join ` K )
  assume oldmm1.m: |- ./\ = ( meet ` K )
  assume oldmm1.o: |- ._|_ = ( oc ` K )


  assert |- ( ( K e. OL /\ X e. B /\ Y e. B ) -> ( ._|_ ` ( X ./\ Y ) ) = ( ( ._|_ ` X ) .\/ ( ._|_ ` Y ) ) )

  proof
    cK
    col
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
    cB
    cK
    cK
    cple
    cfv
    #
    cX
    cY
    c.an
    co
    #
    c.pe
    cfv
    #
    cX
    c.pe
    cfv
    #
    cY
    c.pe
    cfv
    #
    c.or
    co
    #
    oldmm1.b
    @4
    eqid
    #
    @0
    @1
    cK
    clat
    wcel
    #
    @2
    cK
    ollat
    #
    3ad2ant1
    #
    @3
    cK
    cops
    wcel
    #
    @5
    cB
    wcel
    #
    @6
    cB
    wcel
    #
    @0
    @1
    @14
    @2
    cK
    olop
    #
    3ad2ant1
    #
    @0
    @11
    @1
    @2
    @15
    @12
    cB
    cK
    c.an
    cX
    cY
    oldmm1.b
    oldmm1.m
    latmcl
    syl3an1
    #
    cB
    cK
    c.pe
    @5
    oldmm1.b
    oldmm1.o
    opoccl
    syl2anc
    #
    @3
    @11
    @7
    cB
    wcel
    #
    @8
    cB
    wcel
    #
    @9
    cB
    wcel
    #
    @13
    @0
    @1
    @21
    @2
    @0
    @14
    @1
    @21
    @17
    cB
    cK
    c.pe
    cX
    oldmm1.b
    oldmm1.o
    opoccl
    sylan
    3adant3
    #
    @0
    @2
    @22
    @1
    @0
    @14
    @2
    @22
    @17
    cB
    cK
    c.pe
    cY
    oldmm1.b
    oldmm1.o
    opoccl
    sylan
    3adant2
    #
    cB
    c.or
    cK
    @7
    @8
    oldmm1.b
    oldmm1.j
    latjcl
    syl3anc
    #
    @3
    @9
    c.pe
    cfv
    #
    @5
    @4
    wbr
    #
    @6
    @9
    @4
    wbr
    #
    @3
    @27
    cX
    @4
    wbr
    #
    @27
    cY
    @4
    wbr
    #
    @28
    @3
    @7
    @9
    @4
    wbr
    #
    @30
    @3
    @11
    @21
    @22
    @32
    @13
    @24
    @25
    cB
    c.or
    cK
    @4
    @7
    @8
    oldmm1.b
    @10
    oldmm1.j
    latlej1
    syl3anc
    @3
    @14
    @1
    @23
    @32
    @30
    wb
    @18
    @0
    @1
    @2
    simp2
    #
    @26
    cB
    cK
    @4
    c.pe
    cX
    @9
    oldmm1.b
    @10
    oldmm1.o
    oplecon1b
    syl3anc
    mpbid
    @3
    @8
    @9
    @4
    wbr
    #
    @31
    @3
    @11
    @21
    @22
    @34
    @13
    @24
    @25
    cB
    c.or
    cK
    @4
    @7
    @8
    oldmm1.b
    @10
    oldmm1.j
    latlej2
    syl3anc
    @3
    @14
    @2
    @23
    @34
    @31
    wb
    @18
    @0
    @1
    @2
    simp3
    #
    @26
    cB
    cK
    @4
    c.pe
    cY
    @9
    oldmm1.b
    @10
    oldmm1.o
    oplecon1b
    syl3anc
    mpbid
    @3
    @11
    @27
    cB
    wcel
    #
    @1
    @2
    @30
    @31
    wa
    @28
    wb
    @13
    @3
    @14
    @23
    @36
    @18
    @26
    cB
    cK
    c.pe
    @9
    oldmm1.b
    oldmm1.o
    opoccl
    syl2anc
    @33
    @35
    cB
    cK
    @4
    c.an
    @27
    cX
    cY
    oldmm1.b
    @10
    oldmm1.m
    latlem12
    syl13anc
    mpbi2and
    @3
    @14
    @23
    @15
    @28
    @29
    wb
    @18
    @26
    @19
    cB
    cK
    @4
    c.pe
    @9
    @5
    oldmm1.b
    @10
    oldmm1.o
    oplecon1b
    syl3anc
    mpbid
    @3
    @7
    @6
    @4
    wbr
    #
    @8
    @6
    @4
    wbr
    #
    @9
    @6
    @4
    wbr
    #
    @3
    @5
    cX
    @4
    wbr
    #
    @37
    @0
    @11
    @1
    @2
    @40
    @12
    cB
    cK
    @4
    c.an
    cX
    cY
    oldmm1.b
    @10
    oldmm1.m
    latmle1
    syl3an1
    @3
    @14
    @15
    @1
    @40
    @37
    wb
    @18
    @19
    @33
    cB
    cK
    @4
    c.pe
    @5
    cX
    oldmm1.b
    @10
    oldmm1.o
    oplecon3b
    syl3anc
    mpbid
    @3
    @5
    cY
    @4
    wbr
    #
    @38
    @0
    @11
    @1
    @2
    @41
    @12
    cB
    cK
    @4
    c.an
    cX
    cY
    oldmm1.b
    @10
    oldmm1.m
    latmle2
    syl3an1
    @3
    @14
    @15
    @2
    @41
    @38
    wb
    @18
    @19
    @35
    cB
    cK
    @4
    c.pe
    @5
    cY
    oldmm1.b
    @10
    oldmm1.o
    oplecon3b
    syl3anc
    mpbid
    @3
    @11
    @21
    @22
    @16
    @37
    @38
    wa
    @39
    wb
    @13
    @24
    @25
    @20
    cB
    c.or
    cK
    @4
    @7
    @8
    @6
    oldmm1.b
    @10
    oldmm1.j
    latjle12
    syl13anc
    mpbi2and
    latasymd
end
