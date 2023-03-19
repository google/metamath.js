include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "co.mm"
include "simp132.mm"
include "simp111.mm"
include "simp2l.mm"
include "simp12l.mm"
include "3jca.mm"
include "simp2rr.mm"
include "pltle.mm"
include "sylc.mm"
include "clat.mm"
include "wb.mm"
include "hllat.mm"
include "syl.mm"
include "simp3l.mm"
include "atbase.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "biimpd.mm"
include "mpan2d.mm"
include "simp112.mm"
include "simp3r2.mm"
include "simp3r3.mm"
include "hlatexch2.mm"
include "wi.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "lattr.mm"
include "mpand.mm"
include "syld.mm"
include "mtod.mm"
include "simp2rl.mm"
include "wceq.mm"
include "simp113.mm"
include "simp3r1.mm"
include "hlatexchb1.mm"
include "syl131anc.mm"
include "hlatexch1.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "sylbid.mm"
include "jctird.mm"
include "latlem12.mm"
include "breq2i.mm"
include "syl6bbr.mm"
include "sylibd.mm"
include "cal.mm"
include "hlatl.mm"
include "simp12r.mm"
include "simp131.mm"
include "1cvrat.mm"
include "syl133anc.mm"
include "syl5eqel.mm"
include "atcmp.mm"
include "necon3ad.mm"
include "mpd.mm"
include "jca.mm"

theorem cdlemblem
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let c.lt: class .<
  let c.1: class .1.
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cX: class X
  let vr: setvar r
  assume cdlemb.b: |- B = ( Base ` K )
  assume cdlemb.l: |- .<_ = ( le ` K )
  assume cdlemb.j: |- .\/ = ( join ` K )
  assume cdlemb.u: |- .1. = ( 1. ` K )
  assume cdlemb.c: |- C = ( <o ` K )
  assume cdlemb.a: |- A = ( Atoms ` K )
  assume cdlemblem.s: |- .< = ( lt ` K )
  assume cdlemblem.m: |- ./\ = ( meet ` K )
  assume cdlemblem.v: |- V = ( ( P .\/ Q ) ./\ X )


  assert |- ( ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( X e. B /\ P =/= Q ) /\ ( X C .1. /\ -. P .<_ X /\ -. Q .<_ X ) ) /\ ( u e. A /\ ( u =/= V /\ u .< X ) ) /\ ( r e. A /\ ( r =/= P /\ r =/= u /\ r .<_ ( P .\/ u ) ) ) ) -> ( -. r .<_ X /\ -. r .<_ ( P .\/ Q ) ) )

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
    cA
    wcel
    #
    @13
    cV
    wne
    #
    @13
    cX
    c.lt
    wbr
    #
    wa
    #
    wa
    #
    vr
    cv
    #
    cA
    wcel
    #
    @19
    cP
    wne
    #
    @19
    @13
    wne
    #
    @19
    cP
    @13
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    wa
    #
    w3a
    #
    @19
    cX
    c.le
    wbr
    #
    wn
    @19
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    @26
    @27
    @8
    @7
    @9
    @10
    @3
    @6
    @18
    @25
    simp132
    #
    @26
    @27
    @19
    @13
    c.or
    co
    #
    cX
    c.le
    wbr
    #
    @8
    @26
    @27
    @13
    cX
    c.le
    wbr
    #
    @33
    @26
    @0
    @14
    @4
    w3a
    @16
    @34
    @26
    @0
    @14
    @4
    @0
    @1
    @2
    @6
    @11
    @18
    @25
    simp111
    #
    @12
    @14
    @17
    @25
    simp2l
    #
    @4
    @5
    @3
    @11
    @18
    @25
    simp12l
    #
    3jca
    @15
    @16
    @14
    @12
    @25
    simp2rr
    chlt
    cA
    cB
    c.lt
    cK
    c.le
    @13
    cX
    cdlemb.l
    cdlemblem.s
    pltle
    sylc
    #
    @26
    @27
    @34
    wa
    #
    @33
    @26
    cK
    clat
    wcel
    #
    @19
    cB
    wcel
    #
    @13
    cB
    wcel
    #
    @4
    @39
    @33
    wb
    @26
    @0
    @40
    @35
    cK
    hllat
    syl
    #
    @26
    @20
    @41
    @12
    @18
    @20
    @24
    simp3l
    #
    cA
    cB
    @19
    cK
    cdlemb.b
    cdlemb.a
    atbase
    syl
    #
    @26
    @14
    @42
    @36
    cA
    cB
    @13
    cK
    cdlemb.b
    cdlemb.a
    atbase
    syl
    #
    @37
    cB
    c.or
    cK
    c.le
    @19
    @13
    cX
    cdlemb.b
    cdlemb.l
    cdlemb.j
    latjle12
    syl13anc
    biimpd
    mpan2d
    @26
    cP
    @32
    c.le
    wbr
    #
    @33
    @8
    @26
    @0
    @20
    @1
    @14
    w3a
    #
    @22
    w3a
    @23
    @47
    @26
    @0
    @48
    @22
    @35
    @26
    @20
    @1
    @14
    @44
    @0
    @1
    @2
    @6
    @11
    @18
    @25
    simp112
    #
    @36
    3jca
    @21
    @22
    @23
    @20
    @12
    @18
    simp3r2
    3jca
    @21
    @22
    @23
    @20
    @12
    @18
    simp3r3
    #
    cA
    @19
    cP
    @13
    c.or
    cK
    c.le
    cdlemb.l
    cdlemb.j
    cdlemb.a
    hlatexch2
    sylc
    @26
    @40
    cP
    cB
    wcel
    #
    @32
    cB
    wcel
    #
    @4
    @47
    @33
    wa
    @8
    wi
    @43
    @26
    @1
    @51
    @49
    cA
    cB
    cP
    cK
    cdlemb.b
    cdlemb.a
    atbase
    syl
    #
    @26
    @40
    @41
    @42
    @52
    @43
    @45
    @46
    cB
    c.or
    cK
    @19
    @13
    cdlemb.b
    cdlemb.j
    latjcl
    syl3anc
    @37
    cB
    cK
    c.le
    cP
    @32
    cX
    cdlemb.b
    cdlemb.l
    lattr
    syl13anc
    mpand
    syld
    mtod
    @26
    @15
    @30
    @15
    @16
    @14
    @12
    @25
    simp2rl
    @26
    @29
    @13
    cV
    @26
    @29
    @13
    cV
    c.le
    wbr
    #
    @13
    cV
    wceq
    #
    @26
    @29
    @13
    @28
    c.le
    wbr
    #
    @34
    wa
    #
    @54
    @26
    @29
    @56
    @34
    @26
    @29
    cP
    @19
    c.or
    co
    #
    @28
    wceq
    #
    @56
    @26
    @0
    @20
    @2
    @1
    @21
    @29
    @59
    wb
    @35
    @44
    @0
    @1
    @2
    @6
    @11
    @18
    @25
    simp113
    #
    @49
    @21
    @22
    @23
    @20
    @12
    @18
    simp3r1
    #
    cA
    @19
    cQ
    cP
    c.or
    cK
    c.le
    cdlemb.l
    cdlemb.j
    cdlemb.a
    hlatexchb1
    syl131anc
    @26
    @13
    @58
    c.le
    wbr
    #
    @59
    @56
    @26
    @0
    @20
    @14
    @1
    w3a
    #
    @21
    w3a
    @23
    @62
    @26
    @0
    @63
    @21
    @35
    @26
    @20
    @14
    @1
    @44
    @36
    @49
    3jca
    @61
    3jca
    @50
    cA
    @19
    @13
    cP
    c.or
    cK
    c.le
    cdlemb.l
    cdlemb.j
    cdlemb.a
    hlatexch1
    sylc
    @58
    @28
    @13
    c.le
    breq2
    syl5ibcom
    sylbid
    @38
    jctird
    @26
    @57
    @13
    @28
    cX
    c.an
    co
    #
    c.le
    wbr
    #
    @54
    @26
    @40
    @42
    @28
    cB
    wcel
    #
    @4
    @57
    @65
    wb
    @43
    @46
    @26
    @40
    @51
    cQ
    cB
    wcel
    #
    @66
    @43
    @53
    @26
    @2
    @67
    @60
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
    @37
    cB
    cK
    c.le
    c.an
    @13
    @28
    cX
    cdlemb.b
    cdlemb.l
    cdlemblem.m
    latlem12
    syl13anc
    cV
    @64
    @13
    c.le
    cdlemblem.v
    breq2i
    syl6bbr
    sylibd
    @26
    cK
    cal
    wcel
    #
    @14
    cV
    cA
    wcel
    @54
    @55
    wb
    @26
    @0
    @68
    @35
    cK
    hlatl
    syl
    @36
    @26
    cV
    @64
    cA
    cdlemblem.v
    @26
    @0
    @1
    @2
    @4
    @5
    @7
    @9
    @64
    cA
    wcel
    @35
    @49
    @60
    @37
    @4
    @5
    @3
    @11
    @18
    @25
    simp12r
    @7
    @9
    @10
    @3
    @6
    @18
    @25
    simp131
    @31
    cA
    cB
    cC
    cP
    cQ
    c.1
    c.or
    cK
    c.le
    c.an
    cX
    cdlemb.b
    cdlemb.l
    cdlemb.j
    cdlemblem.m
    cdlemb.u
    cdlemb.c
    cdlemb.a
    1cvrat
    syl133anc
    syl5eqel
    cA
    @13
    cV
    cK
    c.le
    cdlemb.l
    cdlemb.a
    atcmp
    syl3anc
    sylibd
    necon3ad
    mpd
    jca
end
