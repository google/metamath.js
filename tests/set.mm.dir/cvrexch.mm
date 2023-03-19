include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "cvrexchlem.mm"
include "coc.mm"
include "cfv.mm"
include "wi.mm"
include "simp1.mm"
include "cops.mm"
include "hlop.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "eqid.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "simp2.mm"
include "syl3anc.mm"
include "col.mm"
include "wceq.mm"
include "hlol.mm"
include "oldmj1.mm"
include "syl3an1.mm"
include "clat.mm"
include "hllat.mm"
include "latmcom.mm"
include "eqtrd.mm"
include "breq1d.mm"
include "oldmm1.mm"
include "latjcom.mm"
include "breq2d.mm"
include "3imtr4d.mm"
include "wb.mm"
include "latjcl.mm"
include "cvrcon3b.mm"
include "latmcl.mm"
include "impbid.mm"

theorem cvrexch
  let cB: class B
  let cC: class C
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume cvrexch.b: |- B = ( Base ` K )
  assume cvrexch.j: |- .\/ = ( join ` K )
  assume cvrexch.m: |- ./\ = ( meet ` K )
  assume cvrexch.c: |- C = ( <o ` K )


  assert |- ( ( K e. HL /\ X e. B /\ Y e. B ) -> ( ( X ./\ Y ) C Y <-> X C ( X .\/ Y ) ) )

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
    cX
    cY
    c.an
    co
    #
    cY
    cC
    wbr
    #
    cX
    cX
    cY
    c.or
    co
    #
    cC
    wbr
    #
    cB
    cC
    c.or
    cK
    c.an
    cX
    cY
    cvrexch.b
    cvrexch.j
    cvrexch.m
    cvrexch.c
    cvrexchlem
    @3
    @6
    cK
    coc
    cfv
    #
    cfv
    #
    cX
    @8
    cfv
    #
    cC
    wbr
    #
    cY
    @8
    cfv
    #
    @4
    @8
    cfv
    #
    cC
    wbr
    #
    @7
    @5
    @3
    @12
    @10
    c.an
    co
    #
    @10
    cC
    wbr
    #
    @12
    @12
    @10
    c.or
    co
    #
    cC
    wbr
    #
    @11
    @14
    @3
    @0
    @12
    cB
    wcel
    #
    @10
    cB
    wcel
    #
    @16
    @18
    wi
    @0
    @1
    @2
    simp1
    @3
    cK
    cops
    wcel
    #
    @2
    @19
    @0
    @1
    @21
    @2
    cK
    hlop
    3ad2ant1
    #
    @0
    @1
    @2
    simp3
    #
    cB
    cK
    @8
    cY
    cvrexch.b
    @8
    eqid
    #
    opoccl
    syl2anc
    #
    @3
    @21
    @1
    @20
    @22
    @0
    @1
    @2
    simp2
    #
    cB
    cK
    @8
    cX
    cvrexch.b
    @24
    opoccl
    syl2anc
    #
    cB
    cC
    c.or
    cK
    c.an
    @12
    @10
    cvrexch.b
    cvrexch.j
    cvrexch.m
    cvrexch.c
    cvrexchlem
    syl3anc
    @3
    @9
    @15
    @10
    cC
    @3
    @9
    @10
    @12
    c.an
    co
    #
    @15
    @0
    cK
    col
    wcel
    #
    @1
    @2
    @9
    @28
    wceq
    cK
    hlol
    #
    cB
    c.or
    cK
    c.an
    @8
    cX
    cY
    cvrexch.b
    cvrexch.j
    cvrexch.m
    @24
    oldmj1
    syl3an1
    @3
    cK
    clat
    wcel
    #
    @20
    @19
    @28
    @15
    wceq
    @0
    @1
    @31
    @2
    cK
    hllat
    #
    3ad2ant1
    #
    @27
    @25
    cB
    cK
    c.an
    @10
    @12
    cvrexch.b
    cvrexch.m
    latmcom
    syl3anc
    eqtrd
    breq1d
    @3
    @13
    @17
    @12
    cC
    @3
    @13
    @10
    @12
    c.or
    co
    #
    @17
    @0
    @29
    @1
    @2
    @13
    @34
    wceq
    @30
    cB
    c.or
    cK
    c.an
    @8
    cX
    cY
    cvrexch.b
    cvrexch.j
    cvrexch.m
    @24
    oldmm1
    syl3an1
    @3
    @31
    @20
    @19
    @34
    @17
    wceq
    @33
    @27
    @25
    cB
    c.or
    cK
    @10
    @12
    cvrexch.b
    cvrexch.j
    latjcom
    syl3anc
    eqtrd
    breq2d
    3imtr4d
    @3
    @21
    @1
    @6
    cB
    wcel
    #
    @7
    @11
    wb
    @22
    @26
    @0
    @31
    @1
    @2
    @35
    @32
    cB
    c.or
    cK
    cX
    cY
    cvrexch.b
    cvrexch.j
    latjcl
    syl3an1
    cB
    cC
    cK
    @8
    cX
    @6
    cvrexch.b
    @24
    cvrexch.c
    cvrcon3b
    syl3anc
    @3
    @21
    @4
    cB
    wcel
    #
    @2
    @5
    @14
    wb
    @22
    @0
    @31
    @1
    @2
    @36
    @32
    cB
    cK
    c.an
    cX
    cY
    cvrexch.b
    cvrexch.m
    latmcl
    syl3an1
    @23
    cB
    cC
    cK
    @8
    @4
    cY
    cvrexch.b
    @24
    cvrexch.c
    cvrcon3b
    syl3anc
    3imtr4d
    impbid
end
