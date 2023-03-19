include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "cin.mm"
include "c0g.mm"
include "csn.mm"
include "incom.mm"
include "eqid.mm"
include "dihmeetlem18N.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2l.mm"
include "simpl3.mm"
include "simpr1.mm"
include "simpr31.mm"
include "simpr33.mm"
include "dihmeetlem12N.mm"
include "syl33anc.mm"
include "csubg.mm"
include "clmod.mm"
include "clss.mm"
include "dvhlmod.mm"
include "clat.mm"
include "simpl1l.mm"
include "hllat.mm"
include "syl.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "dihlss.mm"
include "syl2anc.mm"
include "lsssubg.mm"
include "lsm01.mm"
include "3eqtr3rd.mm"

theorem dihmeetlem19N
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) /\ Y e. B ) /\ ( ( p e. A /\ -. p .<_ W ) /\ ( r e. A /\ -. r .<_ W ) /\ ( p .<_ X /\ r .<_ Y /\ ( X ./\ Y ) .<_ W ) ) ) -> ( I ` ( X ./\ Y ) ) = ( ( I ` X ) i^i ( I ` Y ) ) )

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
    cX
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cY
    cB
    wcel
    #
    w3a
    #
    vp
    cv
    #
    cA
    wcel
    @8
    cW
    c.le
    wbr
    wn
    wa
    #
    vr
    cv
    #
    cA
    wcel
    @10
    cW
    c.le
    wbr
    wn
    wa
    #
    @8
    cX
    c.le
    wbr
    #
    @10
    cY
    c.le
    wbr
    #
    cX
    cY
    c.an
    co
    #
    cW
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    wa
    #
    @14
    cI
    cfv
    #
    @8
    cI
    cfv
    #
    cY
    cI
    cfv
    #
    cin
    #
    c.po
    co
    #
    @19
    cU
    c0g
    cfv
    #
    csn
    #
    c.po
    co
    #
    cX
    cI
    cfv
    @21
    cin
    #
    @19
    @18
    @22
    @25
    @19
    c.po
    @18
    @22
    @21
    @20
    cin
    @25
    @20
    @21
    incom
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
    cX
    cY
    @24
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
    @24
    eqid
    #
    dihmeetlem18N
    syl5eq
    oveq2d
    @18
    @2
    @3
    @6
    @9
    @12
    @15
    @23
    @27
    wceq
    @2
    @5
    @6
    @17
    simpl1
    #
    @3
    @4
    @2
    @6
    @17
    simpl2l
    #
    @2
    @5
    @6
    @17
    simpl3
    #
    @7
    @9
    @11
    @16
    simpr1
    @12
    @13
    @15
    @9
    @11
    @7
    simpr31
    @12
    @13
    @15
    @9
    @11
    @7
    simpr33
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
    cX
    cY
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
    dihmeetlem12N
    syl33anc
    @18
    @19
    cU
    csubg
    cfv
    wcel
    #
    @26
    @19
    wceq
    @18
    cU
    clmod
    wcel
    @19
    cU
    clss
    cfv
    #
    wcel
    #
    @32
    @18
    cU
    cH
    cK
    cW
    dihmeetlem14.h
    dihmeetlem14.u
    @29
    dvhlmod
    @18
    @2
    @14
    cB
    wcel
    #
    @34
    @29
    @18
    cK
    clat
    wcel
    #
    @3
    @6
    @35
    @18
    @0
    @36
    @0
    @1
    @5
    @6
    @17
    simpl1l
    cK
    hllat
    syl
    @30
    @31
    cB
    cK
    c.an
    cX
    cY
    dihmeetlem14.b
    dihmeetlem14.m
    latmcl
    syl3anc
    cB
    @33
    cU
    cH
    cI
    cK
    cW
    @14
    dihmeetlem14.b
    dihmeetlem14.h
    dihmeetlem14.i
    dihmeetlem14.u
    @33
    eqid
    #
    dihlss
    syl2anc
    @33
    @19
    cU
    @37
    lsssubg
    syl2anc
    c.po
    cU
    @19
    @24
    @28
    dihmeetlem14.s
    lsm01
    syl
    3eqtr3rd
end
