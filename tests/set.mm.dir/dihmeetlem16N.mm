include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cin.mm"
include "c0g.mm"
include "csn.mm"
include "eqid.mm"
include "dihmeetlem15N.mm"
include "oveq2d.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3l.mm"
include "atbase.mm"
include "syl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "dihmeetlem14N.mm"
include "syl33anc.mm"
include "csubg.mm"
include "clmod.mm"
include "clss.mm"
include "dvhlmod.mm"
include "clat.mm"
include "simpl1l.mm"
include "hllat.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "dihlss.mm"
include "syl2anc.mm"
include "lsssubg.mm"
include "lsm01.mm"
include "3eqtr3rd.mm"

theorem dihmeetlem16N
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
  let cY: class Y
  let vr: setvar r
  let vp: setvar p
  let vh: setvar h
  assume dihmeetlem14.b: |- B = ( Base ` K )
  assume dihmeetlem14.l: |- .<_ = ( le ` K )
  assume dihmeetlem14.h: |- H = ( LHyp ` K )
  assume dihmeetlem14.j: |- .\/ = ( join ` K )
  assume dihmeetlem14.m: |- ./\ = ( meet ` K )
  assume dihmeetlem14.a: |- A = ( Atoms ` K )
  assume dihmeetlem14.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihmeetlem14.s: |- .(+) = ( LSSum ` U )
  assume dihmeetlem14.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ Y e. B /\ ( p e. A /\ -. p .<_ W ) ) /\ ( ( r e. A /\ -. r .<_ W ) /\ r .<_ Y /\ ( Y ./\ p ) .<_ W ) ) -> ( I ` ( Y ./\ p ) ) = ( ( I ` Y ) i^i ( I ` p ) ) )

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
    cY
    cB
    wcel
    #
    vp
    cv
    #
    cA
    wcel
    #
    @4
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    vr
    cv
    #
    cA
    wcel
    @9
    cW
    c.le
    wbr
    wn
    wa
    #
    @9
    cY
    c.le
    wbr
    #
    cY
    @4
    c.an
    co
    #
    cW
    c.le
    wbr
    #
    w3a
    #
    wa
    #
    @12
    cI
    cfv
    #
    @9
    cI
    cfv
    @4
    cI
    cfv
    #
    cin
    #
    c.po
    co
    #
    @16
    cU
    c0g
    cfv
    #
    csn
    #
    c.po
    co
    #
    cY
    cI
    cfv
    @17
    cin
    #
    @16
    @15
    @18
    @21
    @16
    c.po
    cA
    cB
    c.po
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cW
    cY
    @20
    vr
    vp
    dihmeetlem14.b
    dihmeetlem14.l
    dihmeetlem14.h
    dihmeetlem14.j
    dihmeetlem14.m
    dihmeetlem14.a
    dihmeetlem14.u
    dihmeetlem14.s
    dihmeetlem14.i
    @20
    eqid
    #
    dihmeetlem15N
    oveq2d
    @15
    @2
    @3
    @4
    cB
    wcel
    #
    @10
    @11
    @13
    @19
    @23
    wceq
    @2
    @3
    @7
    @14
    simpl1
    #
    @2
    @3
    @7
    @14
    simpl2
    #
    @15
    @5
    @25
    @5
    @6
    @2
    @3
    @14
    simpl3l
    cA
    cB
    @4
    cK
    dihmeetlem14.b
    dihmeetlem14.a
    atbase
    syl
    #
    @8
    @10
    @11
    @13
    simpr1
    @8
    @10
    @11
    @13
    simpr2
    @8
    @10
    @11
    @13
    simpr3
    cA
    cB
    c.po
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cW
    cY
    vr
    vp
    dihmeetlem14.b
    dihmeetlem14.l
    dihmeetlem14.h
    dihmeetlem14.j
    dihmeetlem14.m
    dihmeetlem14.a
    dihmeetlem14.u
    dihmeetlem14.s
    dihmeetlem14.i
    dihmeetlem14N
    syl33anc
    @15
    @16
    cU
    csubg
    cfv
    wcel
    #
    @22
    @16
    wceq
    @15
    cU
    clmod
    wcel
    @16
    cU
    clss
    cfv
    #
    wcel
    #
    @29
    @15
    cU
    cH
    cK
    cW
    dihmeetlem14.h
    dihmeetlem14.u
    @26
    dvhlmod
    @15
    @2
    @12
    cB
    wcel
    #
    @31
    @26
    @15
    cK
    clat
    wcel
    #
    @3
    @25
    @32
    @15
    @0
    @33
    @0
    @1
    @3
    @7
    @14
    simpl1l
    cK
    hllat
    syl
    @27
    @28
    cB
    cK
    c.an
    cY
    @4
    dihmeetlem14.b
    dihmeetlem14.m
    latmcl
    syl3anc
    cB
    @30
    cU
    cH
    cI
    cK
    cW
    @12
    dihmeetlem14.b
    dihmeetlem14.h
    dihmeetlem14.i
    dihmeetlem14.u
    @30
    eqid
    #
    dihlss
    syl2anc
    @30
    @16
    cU
    @34
    lsssubg
    syl2anc
    c.po
    cU
    @16
    @20
    @24
    dihmeetlem14.s
    lsm01
    syl
    3eqtr3rd
end
