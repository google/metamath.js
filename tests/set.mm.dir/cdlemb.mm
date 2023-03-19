include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "co.mm"
include "cmee.mm"
include "cfv.mm"
include "cplt.mm"
include "wrex.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp31.mm"
include "simp32.mm"
include "eqid.mm"
include "1cvrat.mm"
include "syl133anc.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "latmle2.mm"
include "1cvratlt.mm"
include "syl32anc.mm"
include "2atlt.mm"
include "syl31anc.mm"
include "simpl11.mm"
include "simpl12.mm"
include "simprl.mm"
include "simpl32.mm"
include "wceq.mm"
include "simprrr.mm"
include "wi.mm"
include "simpl2l.mm"
include "pltle.mm"
include "mpd.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "necon3bd.mm"
include "hlsupr.mm"
include "cdlemblem.mm"
include "3exp.mm"
include "exp4a.mm"
include "imp.mm"
include "reximdvai.mm"
include "rexlimddv.mm"

theorem cdlemb
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let c.1: class .1.
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vr: setvar r
  let vu: setvar u
  assume cdlemb.b: |- B = ( Base ` K )
  assume cdlemb.l: |- .<_ = ( le ` K )
  assume cdlemb.j: |- .\/ = ( join ` K )
  assume cdlemb.u: |- .1. = ( 1. ` K )
  assume cdlemb.c: |- C = ( <o ` K )
  assume cdlemb.a: |- A = ( Atoms ` K )

  disjoint A r
  disjoint B r
  disjoint C r
  disjoint .\/ r
  disjoint K r
  disjoint .<_ r
  disjoint P r
  disjoint Q r
  disjoint .1. r
  disjoint X r
  disjoint r u
  disjoint A u
  disjoint B u
  disjoint C u
  disjoint .\/ u
  disjoint K u
  disjoint .<_ u
  disjoint P u
  disjoint Q u
  disjoint .1. u
  disjoint X u
  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( X e. B /\ P =/= Q ) /\ ( X C .1. /\ -. P .<_ X /\ -. Q .<_ X ) ) -> E. r e. A ( -. r .<_ X /\ -. r .<_ ( P .\/ Q ) ) )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    w3a
    #
    cX
    cB
    wcel
    #
    cP
    cQ
    wne
    #
    wa
    #
    cX
    c.1
    cC
    wbr
    #
    cP
    cX
    c.le
    wbr
    #
    wn
    #
    cQ
    cX
    c.le
    wbr
    wn
    #
    w3a
    #
    w3a
    #
    vu
    cv
    #
    cP
    cQ
    c.or
    co
    #
    cX
    cK
    cmee
    cfv
    #
    co
    #
    wne
    #
    @13
    cX
    cK
    cplt
    cfv
    #
    wbr
    #
    wa
    #
    vr
    cv
    #
    cX
    c.le
    wbr
    wn
    @21
    @14
    c.le
    wbr
    wn
    wa
    #
    vr
    cA
    wrex
    #
    vu
    cA
    @12
    @0
    @16
    cA
    wcel
    #
    @4
    @16
    cX
    @18
    wbr
    #
    @20
    vu
    cA
    wrex
    @0
    @1
    @2
    @6
    @11
    simp11
    #
    @12
    @0
    @1
    @2
    @4
    @5
    @7
    @9
    @24
    @26
    @0
    @1
    @2
    @6
    @11
    simp12
    #
    @0
    @1
    @2
    @6
    @11
    simp13
    #
    @3
    @4
    @5
    @11
    simp2l
    #
    @3
    @4
    @5
    @11
    simp2r
    @3
    @6
    @7
    @9
    @10
    simp31
    #
    @3
    @6
    @7
    @9
    @10
    simp32
    cA
    cB
    cC
    cP
    cQ
    c.1
    c.or
    cK
    c.le
    @15
    cX
    cdlemb.b
    cdlemb.l
    cdlemb.j
    @15
    eqid
    #
    cdlemb.u
    cdlemb.c
    cdlemb.a
    1cvrat
    syl133anc
    #
    @29
    @12
    @0
    @24
    @4
    @7
    @16
    cX
    c.le
    wbr
    #
    @25
    @26
    @32
    @29
    @30
    @12
    cK
    clat
    wcel
    #
    @14
    cB
    wcel
    #
    @4
    @33
    @12
    @0
    @34
    @26
    cK
    hllat
    syl
    #
    @12
    @34
    cP
    cB
    wcel
    #
    cQ
    cB
    wcel
    #
    @35
    @36
    @12
    @1
    @37
    @27
    cA
    cB
    cP
    cK
    cdlemb.b
    cdlemb.a
    atbase
    syl
    @12
    @2
    @38
    @28
    cA
    cB
    cQ
    cK
    cdlemb.b
    cdlemb.a
    atbase
    syl
    cB
    c.or
    cK
    cP
    cQ
    cdlemb.b
    cdlemb.j
    latjcl
    syl3anc
    @29
    cB
    cK
    c.le
    @15
    @14
    cX
    cdlemb.b
    cdlemb.l
    @31
    latmle2
    syl3anc
    cA
    cB
    cC
    @16
    @18
    c.1
    cK
    c.le
    cX
    cdlemb.b
    cdlemb.l
    @18
    eqid
    #
    cdlemb.u
    cdlemb.c
    cdlemb.a
    1cvratlt
    syl32anc
    cA
    cB
    @16
    @18
    cK
    cX
    vu
    cdlemb.b
    @39
    cdlemb.a
    2atlt
    syl31anc
    @12
    @13
    cA
    wcel
    #
    @20
    wa
    #
    wa
    #
    @21
    cP
    wne
    @21
    @13
    wne
    @21
    cP
    @13
    c.or
    co
    c.le
    wbr
    w3a
    #
    vr
    cA
    wrex
    #
    @23
    @42
    @0
    @1
    @40
    cP
    @13
    wne
    #
    @44
    @0
    @1
    @2
    @6
    @11
    @41
    simpl11
    #
    @0
    @1
    @2
    @6
    @11
    @41
    simpl12
    @12
    @40
    @20
    simprl
    #
    @42
    @9
    @45
    @7
    @9
    @10
    @3
    @6
    @41
    simpl32
    @42
    @8
    cP
    @13
    @42
    @8
    cP
    @13
    wceq
    @13
    cX
    c.le
    wbr
    #
    @42
    @19
    @48
    @12
    @40
    @17
    @19
    simprrr
    @42
    @0
    @40
    @4
    @19
    @48
    wi
    @46
    @47
    @4
    @5
    @3
    @11
    @41
    simpl2l
    chlt
    cA
    cB
    @18
    cK
    c.le
    @13
    cX
    cdlemb.l
    @39
    pltle
    syl3anc
    mpd
    cP
    @13
    cX
    c.le
    breq1
    syl5ibrcom
    necon3bd
    mpd
    cA
    cP
    @13
    c.or
    cK
    c.le
    vr
    cdlemb.l
    cdlemb.j
    cdlemb.a
    hlsupr
    syl31anc
    @42
    @43
    @22
    vr
    cA
    @12
    @41
    @21
    cA
    wcel
    #
    @43
    @22
    wi
    wi
    @12
    @41
    @49
    @43
    @22
    @12
    @41
    @49
    @43
    wa
    @22
    vu
    cA
    cB
    cC
    cP
    cQ
    @18
    c.1
    c.or
    cK
    c.le
    @15
    @16
    cX
    vr
    cdlemb.b
    cdlemb.l
    cdlemb.j
    cdlemb.u
    cdlemb.c
    cdlemb.a
    @39
    @31
    @16
    eqid
    cdlemblem
    3exp
    exp4a
    imp
    reximdvai
    mpd
    rexlimddv
end
