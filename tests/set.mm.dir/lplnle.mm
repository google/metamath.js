include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "llnle.mm"
include "3adantr3.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "ccvr.mm"
include "cplt.mm"
include "simp1ll.mm"
include "llnbase.mm"
include "3ad2ant2.mm"
include "simp1lr.mm"
include "simp3.mm"
include "simp2.mm"
include "simp1r3.mm"
include "nelne2.mm"
include "syl2anc.mm"
include "wb.mm"
include "eqid.mm"
include "pltval.mm"
include "syl3anc.mm"
include "mpbir2and.mm"
include "hlrelat3.mm"
include "syl31anc.mm"
include "wi.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "simp21.mm"
include "simp23.mm"
include "atbase.mm"
include "latjcl.mm"
include "simp3l.mm"
include "lplni.mm"
include "simp3r.mm"
include "breq1.mm"
include "rspcev.mm"
include "3exp.mm"
include "3expd.mm"
include "3imp.mm"
include "rexlimdv.mm"
include "mpd.mm"

theorem lplnle
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let vp: setvar p
  let vz: setvar z
  assume lplnle.b: |- B = ( Base ` K )
  assume lplnle.l: |- .<_ = ( le ` K )
  assume lplnle.z: |- .0. = ( 0. ` K )
  assume lplnle.a: |- A = ( Atoms ` K )
  assume lplnle.n: |- N = ( LLines ` K )
  assume lplnle.p: |- P = ( LPlanes ` K )

  disjoint K y
  disjoint .<_ y
  disjoint P y
  disjoint X y
  disjoint p z
  disjoint A p
  disjoint A z
  disjoint B p
  disjoint B z
  disjoint p y
  disjoint K p
  disjoint y z
  disjoint K z
  disjoint .<_ p
  disjoint .<_ z
  disjoint N p
  disjoint N z
  disjoint P p
  disjoint P z
  disjoint X p
  disjoint X z
  disjoint .0. p
  disjoint .0. z
  assert |- ( ( ( K e. HL /\ X e. B ) /\ ( X =/= .0. /\ -. X e. A /\ -. X e. N ) ) -> E. y e. P y .<_ X )

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
    cX
    cN
    wcel
    wn
    #
    w3a
    #
    wa
    #
    vz
    cv
    #
    cX
    c.le
    wbr
    #
    vz
    cN
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
    cP
    wrex
    #
    @2
    @3
    @4
    @10
    @5
    vz
    cA
    cB
    cK
    c.le
    cN
    cX
    c.0
    lplnle.b
    lplnle.l
    lplnle.z
    lplnle.a
    lplnle.n
    llnle
    3adantr3
    @7
    @9
    @13
    vz
    cN
    @7
    @8
    cN
    wcel
    #
    @9
    @13
    @7
    @14
    @9
    w3a
    #
    @8
    @8
    vp
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
    @18
    cX
    c.le
    wbr
    #
    wa
    #
    vp
    cA
    wrex
    #
    @13
    @15
    @0
    @8
    cB
    wcel
    #
    @1
    @8
    cX
    cK
    cplt
    cfv
    #
    wbr
    #
    @23
    @0
    @1
    @6
    @14
    @9
    simp1ll
    #
    @14
    @7
    @24
    @9
    cB
    cK
    cN
    @8
    lplnle.b
    lplnle.n
    llnbase
    #
    3ad2ant2
    @0
    @1
    @6
    @14
    @9
    simp1lr
    #
    @15
    @26
    @9
    @8
    cX
    wne
    #
    @7
    @14
    @9
    simp3
    @15
    @14
    @5
    @30
    @7
    @14
    @9
    simp2
    #
    @3
    @4
    @5
    @2
    @14
    @9
    simp1r3
    @8
    cX
    cN
    nelne2
    syl2anc
    @15
    @0
    @14
    @1
    @26
    @9
    @30
    wa
    wb
    @27
    @31
    @29
    chlt
    cN
    cB
    @25
    cK
    c.le
    @8
    cX
    lplnle.l
    @25
    eqid
    #
    pltval
    syl3anc
    mpbir2and
    cA
    cB
    @19
    @25
    @17
    cK
    c.le
    @8
    cX
    vp
    lplnle.b
    lplnle.l
    @32
    @17
    eqid
    #
    @19
    eqid
    #
    lplnle.a
    hlrelat3
    syl31anc
    @15
    @22
    @13
    vp
    cA
    @7
    @14
    @9
    @16
    cA
    wcel
    #
    @22
    @13
    wi
    #
    wi
    @7
    @14
    @9
    @35
    @36
    @7
    @14
    @9
    @35
    w3a
    #
    @22
    @13
    @7
    @37
    @22
    w3a
    #
    @18
    cP
    wcel
    #
    @21
    @13
    @38
    @0
    @18
    cB
    wcel
    #
    @14
    @20
    @39
    @0
    @1
    @6
    @37
    @22
    simp1ll
    #
    @38
    cK
    clat
    wcel
    #
    @24
    @16
    cB
    wcel
    #
    @40
    @38
    @0
    @42
    @41
    cK
    hllat
    syl
    @38
    @14
    @24
    @7
    @14
    @9
    @35
    @22
    simp21
    #
    @28
    syl
    @38
    @35
    @43
    @7
    @14
    @9
    @35
    @22
    simp23
    cA
    cB
    @16
    cK
    lplnle.b
    lplnle.a
    atbase
    syl
    cB
    @17
    cK
    @8
    @16
    lplnle.b
    @33
    latjcl
    syl3anc
    @44
    @7
    @37
    @20
    @21
    simp3l
    cB
    @19
    chlt
    cP
    cK
    cN
    @8
    @18
    lplnle.b
    @34
    lplnle.n
    lplnle.p
    lplni
    syl31anc
    @7
    @37
    @20
    @21
    simp3r
    @12
    @21
    vy
    @18
    cP
    @11
    @18
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
