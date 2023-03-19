include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "w3a.mm"
include "cv.mm"
include "wrex.mm"
include "cfv.mm"
include "cin.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3ll.mm"
include "simp3r.mm"
include "lhpmcvr6N.mm"
include "syl112anc.mm"
include "simp3l.mm"
include "simp2l.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "latmcom.mm"
include "syl3anc.mm"
include "eqbrtrd.mm"
include "reeanv.mm"
include "simp11.mm"
include "simp12.mm"
include "3ad2ant1.mm"
include "simp3l1.mm"
include "jca.mm"
include "simp2r.mm"
include "simp3r1.mm"
include "simp3l3.mm"
include "simp3r3.mm"
include "simp13r.mm"
include "3jca.mm"
include "dihmeetlem19N.mm"
include "syl33anc.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "syl5bir.mm"
include "mp2and.mm"

theorem dihmeetlem20N
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
  let vh: setvar h
  let vp: setvar p
  let vr: setvar r
  let vq: setvar q
  assume dihmeetlem14.b: |- B = ( Base ` K )
  assume dihmeetlem14.l: |- .<_ = ( le ` K )
  assume dihmeetlem14.h: |- H = ( LHyp ` K )
  assume dihmeetlem14.j: |- .\/ = ( join ` K )
  assume dihmeetlem14.m: |- ./\ = ( meet ` K )
  assume dihmeetlem14.a: |- A = ( Atoms ` K )
  assume dihmeetlem14.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihmeetlem14.s: |- .(+) = ( LSSum ` U )
  assume dihmeetlem14.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) /\ ( ( Y e. B /\ -. Y .<_ W ) /\ ( X ./\ Y ) .<_ W ) ) -> ( I ` ( X ./\ Y ) ) = ( ( I ` X ) i^i ( I ` Y ) ) )

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
    cY
    cW
    c.le
    wbr
    wn
    #
    wa
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
    wa
    #
    w3a
    #
    vq
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @13
    cY
    c.le
    wbr
    wn
    #
    @13
    cX
    c.le
    wbr
    #
    w3a
    #
    vq
    cA
    wrex
    #
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @19
    cX
    c.le
    wbr
    wn
    #
    @19
    cY
    c.le
    wbr
    #
    w3a
    #
    vr
    cA
    wrex
    #
    @9
    cI
    cfv
    cX
    cI
    cfv
    cY
    cI
    cfv
    cin
    wceq
    #
    @12
    @2
    @5
    @6
    @10
    @18
    @2
    @5
    @11
    simp1
    #
    @2
    @5
    @11
    simp2
    @6
    @7
    @10
    @2
    @5
    simp3ll
    #
    @2
    @5
    @8
    @10
    simp3r
    #
    cA
    cB
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    cY
    vq
    dihmeetlem14.b
    dihmeetlem14.l
    dihmeetlem14.j
    dihmeetlem14.m
    dihmeetlem14.a
    dihmeetlem14.h
    lhpmcvr6N
    syl112anc
    @12
    @2
    @8
    @3
    cY
    cX
    c.an
    co
    #
    cW
    c.le
    wbr
    @24
    @26
    @2
    @5
    @8
    @10
    simp3l
    @2
    @3
    @4
    @11
    simp2l
    #
    @12
    @29
    @9
    cW
    c.le
    @12
    cK
    clat
    wcel
    #
    @6
    @3
    @29
    @9
    wceq
    @12
    @0
    @31
    @0
    @1
    @5
    @11
    simp1l
    cK
    hllat
    syl
    @27
    @30
    cB
    cK
    c.an
    cY
    cX
    dihmeetlem14.b
    dihmeetlem14.m
    latmcom
    syl3anc
    @28
    eqbrtrd
    cA
    cB
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cY
    cX
    vr
    dihmeetlem14.b
    dihmeetlem14.l
    dihmeetlem14.j
    dihmeetlem14.m
    dihmeetlem14.a
    dihmeetlem14.h
    lhpmcvr6N
    syl112anc
    @18
    @24
    wa
    @17
    @23
    wa
    #
    vr
    cA
    wrex
    vq
    cA
    wrex
    @12
    @25
    @17
    @23
    vq
    vr
    cA
    cA
    reeanv
    @12
    @32
    @25
    vq
    vr
    cA
    cA
    @12
    @13
    cA
    wcel
    #
    @19
    cA
    wcel
    #
    wa
    #
    @32
    @25
    @12
    @35
    @32
    w3a
    #
    @2
    @5
    @6
    @33
    @14
    wa
    @34
    @20
    wa
    @16
    @22
    @10
    w3a
    @25
    @2
    @5
    @11
    @35
    @32
    simp11
    @2
    @5
    @11
    @35
    @32
    simp12
    @12
    @35
    @6
    @32
    @27
    3ad2ant1
    @36
    @33
    @14
    @12
    @33
    @34
    @32
    simp2l
    @14
    @15
    @16
    @23
    @12
    @35
    simp3l1
    jca
    @36
    @34
    @20
    @12
    @33
    @34
    @32
    simp2r
    @20
    @21
    @22
    @17
    @12
    @35
    simp3r1
    jca
    @36
    @16
    @22
    @10
    @14
    @15
    @16
    @23
    @12
    @35
    simp3l3
    @20
    @21
    @22
    @17
    @12
    @35
    simp3r3
    @8
    @10
    @2
    @5
    @35
    @32
    simp13r
    3jca
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
    vr
    vq
    dihmeetlem14.b
    dihmeetlem14.l
    dihmeetlem14.h
    dihmeetlem14.j
    dihmeetlem14.m
    dihmeetlem14.a
    dihmeetlem14.u
    dihmeetlem14.s
    dihmeetlem14.i
    dihmeetlem19N
    syl33anc
    3exp
    rexlimdvv
    syl5bir
    mp2and
end
