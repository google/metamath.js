include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cin.mm"
include "csubg.mm"
include "wss.mm"
include "wceq.mm"
include "clss.mm"
include "clmod.mm"
include "simp1.mm"
include "dvhlmod.mm"
include "eqid.mm"
include "lsssssubg.mm"
include "syl.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "simp2l.mm"
include "simp2r.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "dihlss.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "atbase.mm"
include "3ad2ant3.mm"
include "wbr.mm"
include "latmle2.mm"
include "wb.mm"
include "dihord.mm"
include "mpbird.mm"
include "lsmmod.mm"
include "syl31anc.mm"
include "cabl.mm"
include "lmodabl.mm"
include "lsmcom.mm"
include "ineq1d.mm"
include "eqtr2d.mm"

theorem dihmeetlem9N
  let cA: class A
  let cB: class B
  let c.po: class .(+)
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume dihmeetlem9.b: |- B = ( Base ` K )
  assume dihmeetlem9.l: |- .<_ = ( le ` K )
  assume dihmeetlem9.h: |- H = ( LHyp ` K )
  assume dihmeetlem9.j: |- .\/ = ( join ` K )
  assume dihmeetlem9.m: |- ./\ = ( meet ` K )
  assume dihmeetlem9.a: |- A = ( Atoms ` K )
  assume dihmeetlem9.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihmeetlem9.s: |- .(+) = ( LSSum ` U )
  assume dihmeetlem9.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ Y e. B ) /\ p e. A ) -> ( ( ( I ` p ) .(+) ( I ` ( X ./\ Y ) ) ) i^i ( I ` Y ) ) = ( ( I ` ( X ./\ Y ) ) .(+) ( ( I ` p ) i^i ( I ` Y ) ) ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
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
    vp
    cv
    #
    cA
    wcel
    #
    w3a
    #
    cX
    cY
    c.an
    co
    #
    cI
    cfv
    #
    @6
    cI
    cfv
    #
    cY
    cI
    cfv
    #
    cin
    c.po
    co
    #
    @10
    @11
    c.po
    co
    #
    @12
    cin
    #
    @11
    @10
    c.po
    co
    #
    @12
    cin
    @8
    @10
    cU
    csubg
    cfv
    #
    wcel
    #
    @11
    @17
    wcel
    #
    @12
    @17
    wcel
    @10
    @12
    wss
    #
    @13
    @15
    wceq
    @8
    cU
    clss
    cfv
    #
    @17
    @10
    @8
    cU
    clmod
    wcel
    #
    @21
    @17
    wss
    @8
    cU
    cH
    cK
    cW
    dihmeetlem9.h
    dihmeetlem9.u
    @2
    @5
    @7
    simp1
    #
    dvhlmod
    #
    @21
    cU
    @21
    eqid
    #
    lsssssubg
    syl
    #
    @8
    @2
    @9
    cB
    wcel
    #
    @10
    @21
    wcel
    @23
    @8
    cK
    clat
    wcel
    #
    @3
    @4
    @27
    @8
    @0
    @28
    @0
    @1
    @5
    @7
    simp1l
    cK
    hllat
    syl
    #
    @2
    @3
    @4
    @7
    simp2l
    #
    @2
    @3
    @4
    @7
    simp2r
    #
    cB
    cK
    c.an
    cX
    cY
    dihmeetlem9.b
    dihmeetlem9.m
    latmcl
    syl3anc
    #
    cB
    @21
    cU
    cH
    cI
    cK
    cW
    @9
    dihmeetlem9.b
    dihmeetlem9.h
    dihmeetlem9.i
    dihmeetlem9.u
    @25
    dihlss
    syl2anc
    sseldd
    #
    @8
    @21
    @17
    @11
    @26
    @8
    @2
    @6
    cB
    wcel
    #
    @11
    @21
    wcel
    @23
    @7
    @2
    @34
    @5
    cA
    cB
    @6
    cK
    dihmeetlem9.b
    dihmeetlem9.a
    atbase
    3ad2ant3
    cB
    @21
    cU
    cH
    cI
    cK
    cW
    @6
    dihmeetlem9.b
    dihmeetlem9.h
    dihmeetlem9.i
    dihmeetlem9.u
    @25
    dihlss
    syl2anc
    sseldd
    #
    @8
    @21
    @17
    @12
    @26
    @8
    @2
    @4
    @12
    @21
    wcel
    @23
    @31
    cB
    @21
    cU
    cH
    cI
    cK
    cW
    cY
    dihmeetlem9.b
    dihmeetlem9.h
    dihmeetlem9.i
    dihmeetlem9.u
    @25
    dihlss
    syl2anc
    sseldd
    @8
    @20
    @9
    cY
    c.le
    wbr
    #
    @8
    @28
    @3
    @4
    @36
    @29
    @30
    @31
    cB
    cK
    c.le
    c.an
    cX
    cY
    dihmeetlem9.b
    dihmeetlem9.l
    dihmeetlem9.m
    latmle2
    syl3anc
    @8
    @2
    @27
    @4
    @20
    @36
    wb
    @23
    @32
    @31
    cB
    cH
    cI
    cK
    c.le
    cW
    @9
    cY
    dihmeetlem9.b
    dihmeetlem9.l
    dihmeetlem9.h
    dihmeetlem9.i
    dihord
    syl3anc
    mpbird
    c.po
    @10
    @11
    @12
    cU
    dihmeetlem9.s
    lsmmod
    syl31anc
    @8
    @14
    @16
    @12
    @8
    cU
    cabl
    wcel
    #
    @18
    @19
    @14
    @16
    wceq
    @8
    @22
    @37
    @24
    cU
    lmodabl
    syl
    @33
    @35
    c.po
    @10
    @11
    cU
    dihmeetlem9.s
    lsmcom
    syl3anc
    ineq1d
    eqtr2d
end
