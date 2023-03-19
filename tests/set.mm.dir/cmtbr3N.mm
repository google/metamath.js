include "coml.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cmtcomN.mm"
include "wb.mm"
include "cmtbr2N.mm"
include "3com23.mm"
include "bitrd.mm"
include "wa.mm"
include "oveq2.mm"
include "adantl.mm"
include "col.mm"
include "omlol.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "clat.mm"
include "omllat.mm"
include "simp3.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "cops.mm"
include "omlop.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "latmassOLD.mm"
include "syl13anc.mm"
include "latjcom.mm"
include "oveq2d.mm"
include "latabs2.mm"
include "syl3an1.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "eqtr3d.mm"
include "adantr.mm"
include "eqtr2d.mm"
include "ex.mm"
include "sylbid.mm"
include "cple.mm"
include "simp1.mm"
include "latmcl.mm"
include "3jca.mm"
include "eqid.mm"
include "latmle1.mm"
include "omllaw2N.mm"
include "sylc.mm"
include "oldmm3N.mm"
include "latmcom.mm"
include "eqeq1d.mm"
include "oveq1.mm"
include "syl6bi.mm"
include "imp.mm"
include "cmtvalN.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem cmtbr3N
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


  assert |- ( ( K e. OML /\ X e. B /\ Y e. B ) -> ( X C Y <-> ( X ./\ ( ( ._|_ ` X ) .\/ Y ) ) = ( X ./\ Y ) ) )

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
    #
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
    @3
    @4
    cY
    cY
    cX
    c.or
    co
    #
    cY
    @5
    c.or
    co
    #
    c.an
    co
    #
    wceq
    #
    @9
    @3
    @4
    cY
    cX
    cC
    wbr
    #
    @13
    cB
    cC
    cK
    cX
    cY
    cmtbr2.b
    cmtbr2.c
    cmtcomN
    @0
    @2
    @1
    @14
    @13
    wb
    cB
    cC
    c.or
    cK
    c.an
    c.pe
    cY
    cX
    cmtbr2.b
    cmtbr2.j
    cmtbr2.m
    cmtbr2.o
    cmtbr2.c
    cmtbr2N
    3com23
    bitrd
    @3
    @13
    @9
    @3
    @13
    wa
    @8
    cX
    @12
    c.an
    co
    #
    @7
    @13
    @8
    @15
    wceq
    @3
    cY
    @12
    cX
    c.an
    oveq2
    adantl
    @3
    @15
    @7
    wceq
    @13
    @3
    cX
    @10
    c.an
    co
    #
    @11
    c.an
    co
    #
    @15
    @7
    @3
    cK
    col
    wcel
    #
    @1
    @10
    cB
    wcel
    #
    @11
    cB
    wcel
    #
    @17
    @15
    wceq
    @0
    @1
    @18
    @2
    cK
    omlol
    #
    3ad2ant1
    @0
    @1
    @2
    simp2
    #
    @3
    cK
    clat
    wcel
    #
    @2
    @1
    @19
    @0
    @1
    @23
    @2
    cK
    omllat
    #
    3ad2ant1
    #
    @0
    @1
    @2
    simp3
    #
    @22
    cB
    c.or
    cK
    cY
    cX
    cmtbr2.b
    cmtbr2.j
    latjcl
    syl3anc
    @3
    @23
    @2
    @5
    cB
    wcel
    #
    @20
    @25
    @26
    @3
    cK
    cops
    wcel
    #
    @1
    @27
    @0
    @1
    @28
    @2
    cK
    omlop
    3ad2ant1
    #
    @22
    cB
    cK
    c.pe
    cX
    cmtbr2.b
    cmtbr2.o
    opoccl
    syl2anc
    #
    cB
    c.or
    cK
    cY
    @5
    cmtbr2.b
    cmtbr2.j
    latjcl
    syl3anc
    cB
    cK
    c.an
    cX
    @10
    @11
    cmtbr2.b
    cmtbr2.m
    latmassOLD
    syl13anc
    @3
    @16
    cX
    @11
    @6
    c.an
    @3
    @16
    cX
    cX
    cY
    c.or
    co
    #
    c.an
    co
    #
    cX
    @3
    @10
    @31
    cX
    c.an
    @3
    @23
    @2
    @1
    @10
    @31
    wceq
    @25
    @26
    @22
    cB
    c.or
    cK
    cY
    cX
    cmtbr2.b
    cmtbr2.j
    latjcom
    syl3anc
    oveq2d
    @0
    @23
    @1
    @2
    @32
    cX
    wceq
    @24
    cB
    c.or
    cK
    c.an
    cX
    cY
    cmtbr2.b
    cmtbr2.j
    cmtbr2.m
    latabs2
    syl3an1
    eqtrd
    @3
    @23
    @2
    @27
    @11
    @6
    wceq
    @25
    @26
    @30
    cB
    c.or
    cK
    cY
    @5
    cmtbr2.b
    cmtbr2.j
    latjcom
    syl3anc
    oveq12d
    eqtr3d
    adantr
    eqtr2d
    ex
    sylbid
    @3
    @9
    cX
    @8
    cX
    cY
    c.pe
    cfv
    #
    c.an
    co
    #
    c.or
    co
    #
    wceq
    #
    @4
    @3
    @9
    @36
    @3
    @9
    wa
    cX
    @34
    c.pe
    cfv
    #
    cX
    c.an
    co
    #
    @34
    c.or
    co
    #
    @35
    @3
    cX
    @39
    wceq
    @9
    @3
    @34
    @38
    c.or
    co
    #
    cX
    @39
    @3
    @0
    @34
    cB
    wcel
    #
    @1
    w3a
    @34
    cX
    cK
    cple
    cfv
    #
    wbr
    #
    @40
    cX
    wceq
    @3
    @0
    @41
    @1
    @0
    @1
    @2
    simp1
    @3
    @23
    @1
    @33
    cB
    wcel
    #
    @41
    @25
    @22
    @3
    @28
    @2
    @44
    @29
    @26
    cB
    cK
    c.pe
    cY
    cmtbr2.b
    cmtbr2.o
    opoccl
    syl2anc
    #
    cB
    cK
    c.an
    cX
    @33
    cmtbr2.b
    cmtbr2.m
    latmcl
    syl3anc
    #
    @22
    3jca
    @3
    @23
    @1
    @44
    @43
    @25
    @22
    @45
    cB
    cK
    @42
    c.an
    cX
    @33
    cmtbr2.b
    @42
    eqid
    #
    cmtbr2.m
    latmle1
    syl3anc
    cB
    c.or
    cK
    @42
    c.an
    c.pe
    @34
    cX
    cmtbr2.b
    @47
    cmtbr2.j
    cmtbr2.m
    cmtbr2.o
    omllaw2N
    sylc
    @3
    @23
    @41
    @38
    cB
    wcel
    #
    @40
    @39
    wceq
    @25
    @46
    @3
    @23
    @37
    cB
    wcel
    #
    @1
    @48
    @25
    @3
    @28
    @41
    @49
    @29
    @46
    cB
    cK
    c.pe
    @34
    cmtbr2.b
    cmtbr2.o
    opoccl
    syl2anc
    #
    @22
    cB
    cK
    c.an
    @37
    cX
    cmtbr2.b
    cmtbr2.m
    latmcl
    syl3anc
    cB
    c.or
    cK
    @34
    @38
    cmtbr2.b
    cmtbr2.j
    latjcom
    syl3anc
    eqtr3d
    adantr
    @3
    @9
    @39
    @35
    wceq
    #
    @3
    @9
    @38
    @8
    wceq
    @51
    @3
    @7
    @38
    @8
    @3
    cX
    @37
    c.an
    co
    #
    @7
    @38
    @3
    @37
    @6
    cX
    c.an
    @0
    @18
    @1
    @2
    @37
    @6
    wceq
    @21
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
    oldmm3N
    syl3an1
    oveq2d
    @3
    @23
    @1
    @49
    @52
    @38
    wceq
    @25
    @22
    @50
    cB
    cK
    c.an
    cX
    @37
    cmtbr2.b
    cmtbr2.m
    latmcom
    syl3anc
    eqtr3d
    eqeq1d
    @38
    @8
    @34
    c.or
    oveq1
    syl6bi
    imp
    eqtrd
    ex
    coml
    cB
    cC
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
    cmtbr2.c
    cmtvalN
    sylibrd
    impbid
end
