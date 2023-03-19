include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "wn.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "simpll.mm"
include "simplr.mm"
include "simprl.mm"
include "atle.mm"
include "syl3anc.mm"
include "w3a.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "ccvr.mm"
include "cplt.mm"
include "simp1ll.mm"
include "atbase.mm"
include "3ad2ant2.mm"
include "simp1lr.mm"
include "simp3.mm"
include "simp2.mm"
include "simp1rr.mm"
include "nelne2.mm"
include "syl2anc.mm"
include "wb.mm"
include "eqid.mm"
include "pltval.mm"
include "mpbir2and.mm"
include "hlrelat3.mm"
include "syl31anc.mm"
include "wi.mm"
include "simp21.mm"
include "simp23.mm"
include "hlatjcl.mm"
include "simp3l.mm"
include "llni.mm"
include "simp3r.mm"
include "breq1.mm"
include "rspcev.mm"
include "3exp.mm"
include "3expd.mm"
include "3imp.mm"
include "rexlimdv.mm"
include "mpd.mm"

theorem llnle
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let vp: setvar p
  let vq: setvar q
  assume llnle.b: |- B = ( Base ` K )
  assume llnle.l: |- .<_ = ( le ` K )
  assume llnle.z: |- .0. = ( 0. ` K )
  assume llnle.a: |- A = ( Atoms ` K )
  assume llnle.n: |- N = ( LLines ` K )

  disjoint K y
  disjoint .<_ y
  disjoint N y
  disjoint X y
  disjoint p q
  disjoint A p
  disjoint A q
  disjoint B p
  disjoint B q
  disjoint p y
  disjoint K p
  disjoint q y
  disjoint K q
  disjoint .<_ p
  disjoint .<_ q
  disjoint N p
  disjoint N q
  disjoint X p
  disjoint X q
  disjoint .0. p
  disjoint .0. q
  assert |- ( ( ( K e. HL /\ X e. B ) /\ ( X =/= .0. /\ -. X e. A ) ) -> E. y e. N y .<_ X )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    c.0
    wne
    #
    cX
    cA
    wcel
    wn
    #
    wa
    #
    wa
    #
    vp
    cv
    #
    cX
    c.le
    wbr
    #
    vp
    cA
    wrex
    #
    vy
    cv
    #
    cX
    c.le
    wbr
    #
    vy
    cN
    wrex
    #
    @6
    @0
    @1
    @3
    @9
    @0
    @1
    @5
    simpll
    @0
    @1
    @5
    simplr
    @2
    @3
    @4
    simprl
    cA
    cB
    cK
    c.le
    cX
    c.0
    vp
    llnle.b
    llnle.l
    llnle.z
    llnle.a
    atle
    syl3anc
    @6
    @8
    @12
    vp
    cA
    @6
    @7
    cA
    wcel
    #
    @8
    @12
    @6
    @13
    @8
    w3a
    #
    @7
    @7
    vq
    cv
    #
    cK
    cjn
    cfv
    #
    co
    #
    cK
    ccvr
    cfv
    #
    wbr
    #
    @17
    cX
    c.le
    wbr
    #
    wa
    #
    vq
    cA
    wrex
    #
    @12
    @14
    @0
    @7
    cB
    wcel
    #
    @1
    @7
    cX
    cK
    cplt
    cfv
    #
    wbr
    #
    @22
    @0
    @1
    @5
    @13
    @8
    simp1ll
    #
    @13
    @6
    @23
    @8
    cA
    cB
    @7
    cK
    llnle.b
    llnle.a
    atbase
    3ad2ant2
    @0
    @1
    @5
    @13
    @8
    simp1lr
    #
    @14
    @25
    @8
    @7
    cX
    wne
    #
    @6
    @13
    @8
    simp3
    @14
    @13
    @4
    @28
    @6
    @13
    @8
    simp2
    #
    @3
    @4
    @2
    @13
    @8
    simp1rr
    @7
    cX
    cA
    nelne2
    syl2anc
    @14
    @0
    @13
    @1
    @25
    @8
    @28
    wa
    wb
    @26
    @29
    @27
    chlt
    cA
    cB
    @24
    cK
    c.le
    @7
    cX
    llnle.l
    @24
    eqid
    #
    pltval
    syl3anc
    mpbir2and
    cA
    cB
    @18
    @24
    @16
    cK
    c.le
    @7
    cX
    vq
    llnle.b
    llnle.l
    @30
    @16
    eqid
    #
    @18
    eqid
    #
    llnle.a
    hlrelat3
    syl31anc
    @14
    @21
    @12
    vq
    cA
    @6
    @13
    @8
    @15
    cA
    wcel
    #
    @21
    @12
    wi
    #
    wi
    @6
    @13
    @8
    @33
    @34
    @6
    @13
    @8
    @33
    w3a
    #
    @21
    @12
    @6
    @35
    @21
    w3a
    #
    @17
    cN
    wcel
    #
    @20
    @12
    @36
    @0
    @17
    cB
    wcel
    #
    @13
    @19
    @37
    @0
    @1
    @5
    @35
    @21
    simp1ll
    #
    @36
    @0
    @13
    @33
    @38
    @39
    @6
    @13
    @8
    @33
    @21
    simp21
    #
    @6
    @13
    @8
    @33
    @21
    simp23
    cA
    cB
    @16
    cK
    @7
    @15
    llnle.b
    @31
    llnle.a
    hlatjcl
    syl3anc
    @40
    @6
    @35
    @19
    @20
    simp3l
    cA
    cB
    @18
    chlt
    @7
    cK
    cN
    @17
    llnle.b
    @32
    llnle.a
    llnle.n
    llni
    syl31anc
    @6
    @35
    @19
    @20
    simp3r
    @11
    @20
    vy
    @17
    cN
    @10
    @17
    cX
    c.le
    breq1
    rspcev
    syl2anc
    3exp
    3expd
    3imp
    rexlimdv
    mpd
    3exp
    rexlimdv
    mpd
end
