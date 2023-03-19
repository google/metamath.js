include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "cv.mm"
include "wn.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "wb.mm"
include "simp1.mm"
include "clat.mm"
include "hllat.mm"
include "latmcl.mm"
include "syl3an1.mm"
include "simp2.mm"
include "cvrval3.mm"
include "syl3anc.mm"
include "3ad2ant1.mm"
include "ad2antrr.mm"
include "atbase.mm"
include "ad2antlr.mm"
include "latlej2.mm"
include "simpr.mm"
include "breqtrd.mm"
include "biantrurd.mm"
include "simpll2.mm"
include "simpll3.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "bitr2d.mm"
include "notbid.mm"
include "ex.mm"
include "pm5.32rd.mm"
include "adantr.mm"
include "adantl.mm"
include "latjcom.mm"
include "eqeq1d.mm"
include "anbi2d.mm"
include "bitrd.mm"
include "rexbidva.mm"

theorem cvrval5
  let cA: class A
  let cB: class B
  let cC: class C
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume cvrval5.b: |- B = ( Base ` K )
  assume cvrval5.l: |- .<_ = ( le ` K )
  assume cvrval5.j: |- .\/ = ( join ` K )
  assume cvrval5.m: |- ./\ = ( meet ` K )
  assume cvrval5.c: |- C = ( <o ` K )
  assume cvrval5.a: |- A = ( Atoms ` K )

  disjoint A p
  disjoint B p
  disjoint C p
  disjoint K p
  disjoint .<_ p
  disjoint ./\ p
  disjoint X p
  disjoint Y p
  assert |- ( ( K e. HL /\ X e. B /\ Y e. B ) -> ( ( X ./\ Y ) C X <-> E. p e. A ( -. p .<_ Y /\ ( p .\/ ( X ./\ Y ) ) = X ) ) )

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
    cX
    cC
    wbr
    #
    vp
    cv
    #
    @4
    c.le
    wbr
    #
    wn
    #
    @4
    @6
    c.or
    co
    #
    cX
    wceq
    #
    wa
    #
    vp
    cA
    wrex
    #
    @6
    cY
    c.le
    wbr
    #
    wn
    #
    @6
    @4
    c.or
    co
    #
    cX
    wceq
    #
    wa
    #
    vp
    cA
    wrex
    @3
    @0
    @4
    cB
    wcel
    #
    @1
    @5
    @12
    wb
    @0
    @1
    @2
    simp1
    @0
    cK
    clat
    wcel
    #
    @1
    @2
    @18
    cK
    hllat
    #
    cB
    cK
    c.an
    cX
    cY
    cvrval5.b
    cvrval5.m
    latmcl
    syl3an1
    #
    @0
    @1
    @2
    simp2
    cA
    cB
    cC
    c.or
    cK
    c.le
    @4
    cX
    vp
    cvrval5.b
    cvrval5.l
    cvrval5.j
    cvrval5.c
    cvrval5.a
    cvrval3
    syl3anc
    @3
    @11
    @17
    vp
    cA
    @3
    @6
    cA
    wcel
    #
    wa
    #
    @11
    @14
    @10
    wa
    @17
    @23
    @10
    @8
    @14
    @23
    @10
    @8
    @14
    wb
    @23
    @10
    wa
    #
    @7
    @13
    @24
    @13
    @6
    cX
    c.le
    wbr
    #
    @13
    wa
    #
    @7
    @24
    @25
    @13
    @24
    @6
    @9
    cX
    c.le
    @24
    @19
    @18
    @6
    cB
    wcel
    #
    @6
    @9
    c.le
    wbr
    @3
    @19
    @22
    @10
    @0
    @1
    @19
    @2
    @20
    3ad2ant1
    #
    ad2antrr
    #
    @3
    @18
    @22
    @10
    @21
    ad2antrr
    @22
    @27
    @3
    @10
    cA
    cB
    @6
    cK
    cvrval5.b
    cvrval5.a
    atbase
    #
    ad2antlr
    #
    cB
    c.or
    cK
    c.le
    @4
    @6
    cvrval5.b
    cvrval5.l
    cvrval5.j
    latlej2
    syl3anc
    @23
    @10
    simpr
    breqtrd
    biantrurd
    @24
    @19
    @27
    @1
    @2
    @26
    @7
    wb
    @29
    @31
    @0
    @1
    @2
    @22
    @10
    simpll2
    @0
    @1
    @2
    @22
    @10
    simpll3
    cB
    cK
    c.le
    c.an
    @6
    cX
    cY
    cvrval5.b
    cvrval5.l
    cvrval5.m
    latlem12
    syl13anc
    bitr2d
    notbid
    ex
    pm5.32rd
    @23
    @10
    @16
    @14
    @23
    @9
    @15
    cX
    @23
    @19
    @18
    @27
    @9
    @15
    wceq
    @3
    @19
    @22
    @28
    adantr
    @3
    @18
    @22
    @21
    adantr
    @22
    @27
    @3
    @30
    adantl
    cB
    c.or
    cK
    @4
    @6
    cvrval5.b
    cvrval5.j
    latjcom
    syl3anc
    eqeq1d
    anbi2d
    bitrd
    rexbidva
    bitrd
end
