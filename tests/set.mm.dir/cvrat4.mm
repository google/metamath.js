include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wceq.mm"
include "wbr.mm"
include "wne.mm"
include "co.mm"
include "cv.mm"
include "wrex.mm"
include "wi.mm"
include "cal.mm"
include "hlatl.mm"
include "adantr.mm"
include "simpr1.mm"
include "atlex.mm"
include "3exp.mm"
include "sylc.mm"
include "simpll.mm"
include "simplr3.mm"
include "simpr.mm"
include "hlatlej1.mm"
include "syl3anc.mm"
include "breq1.mm"
include "syl5ibr.mm"
include "expd.mm"
include "impcom.mm"
include "anim2d.mm"
include "expcomd.mm"
include "reximdvai.mm"
include "syld.mm"
include "ex.mm"
include "a1i.mm"
include "com4l.mm"
include "imp4a.mm"
include "clat.mm"
include "wb.mm"
include "hllat.mm"
include "simpr3.mm"
include "atbase.mm"
include "syl.mm"
include "latleeqj2.mm"
include "biimpa.mm"
include "breq2d.mm"
include "expl.mm"
include "simpl.mm"
include "simpr2.mm"
include "hlatlej2.mm"
include "jctird.mm"
include "jctild.mm"
include "impl.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "adantrl.mm"
include "exp31.mm"
include "wo.mm"
include "wn.mm"
include "ioran.mm"
include "df-ne.mm"
include "anbi1i.mm"
include "bitr4i.mm"
include "cmee.mm"
include "cfv.mm"
include "eqid.mm"
include "cvrat3.mm"
include "3expd.mm"
include "imp4c.mm"
include "latjcl.mm"
include "latmle1.mm"
include "imp44.mm"
include "simplr2.mm"
include "3jca.mm"
include "jca.mm"
include "atnle.mm"
include "latmcom.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "latmcl.mm"
include "latmlem2.mm"
include "breqtrd.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "cops.mm"
include "hlop.mm"
include "ople0.mm"
include "syl2anc.mm"
include "sylibd.mm"
include "sylbid.mm"
include "imp.mm"
include "adantrr.mm"
include "latmle2.mm"
include "latjcom.mm"
include "hlexch3.mm"
include "3expia.mm"
include "syl3c.mm"
include "jcad.mm"
include "syl6.mm"
include "syl5bi.mm"
include "syl7.mm"
include "ecase3d.mm"

theorem cvrat4
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let c.0: class .0.
  let vr: setvar r
  assume cvrat4.b: |- B = ( Base ` K )
  assume cvrat4.l: |- .<_ = ( le ` K )
  assume cvrat4.j: |- .\/ = ( join ` K )
  assume cvrat4.z: |- .0. = ( 0. ` K )
  assume cvrat4.a: |- A = ( Atoms ` K )

  disjoint A r
  disjoint B r
  disjoint .\/ r
  disjoint K r
  disjoint .<_ r
  disjoint P r
  disjoint Q r
  disjoint X r
  assert |- ( ( K e. HL /\ ( X e. B /\ P e. A /\ Q e. A ) ) -> ( ( X =/= .0. /\ P .<_ ( X .\/ Q ) ) -> E. r e. A ( r .<_ X /\ P .<_ ( Q .\/ r ) ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
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
    wa
    #
    cP
    cQ
    wceq
    #
    cQ
    cX
    c.le
    wbr
    #
    cX
    c.0
    wne
    #
    cP
    cX
    cQ
    c.or
    co
    #
    c.le
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
    #
    cP
    cQ
    @12
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    vr
    cA
    wrex
    #
    wi
    @5
    @6
    @8
    @10
    @17
    @10
    @5
    @6
    @8
    @17
    @5
    @6
    @8
    @17
    wi
    #
    wi
    wi
    @10
    @5
    @6
    @18
    @5
    @6
    wa
    #
    @8
    @13
    vr
    cA
    wrex
    #
    @17
    @5
    @8
    @20
    wi
    #
    @6
    @5
    cK
    cal
    wcel
    #
    @1
    @21
    @0
    @22
    @4
    cK
    hlatl
    adantr
    #
    @0
    @1
    @2
    @3
    simpr1
    #
    @22
    @1
    @8
    @20
    vr
    cA
    cB
    cK
    c.le
    cX
    c.0
    cvrat4.b
    cvrat4.l
    cvrat4.z
    cvrat4.a
    atlex
    3exp
    sylc
    adantr
    @19
    @13
    @16
    vr
    cA
    @19
    @13
    @12
    cA
    wcel
    #
    @16
    @19
    @25
    @15
    @13
    @6
    @5
    @25
    @15
    wi
    @6
    @5
    @25
    @15
    @5
    @25
    wa
    #
    @15
    @6
    cQ
    @14
    c.le
    wbr
    #
    @26
    @0
    @3
    @25
    @27
    @0
    @4
    @25
    simpll
    @1
    @2
    @3
    @0
    @25
    simplr3
    @5
    @25
    simpr
    cA
    cQ
    @12
    c.or
    cK
    c.le
    cvrat4.l
    cvrat4.j
    cvrat4.a
    hlatlej1
    syl3anc
    cP
    cQ
    @14
    c.le
    breq1
    syl5ibr
    expd
    impcom
    anim2d
    expcomd
    reximdvai
    syld
    ex
    a1i
    com4l
    imp4a
    @5
    @7
    @11
    @17
    @5
    @7
    wa
    #
    @10
    @17
    @8
    @28
    @10
    wa
    @2
    cP
    cX
    c.le
    wbr
    #
    cP
    cQ
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    wa
    #
    @17
    @5
    @7
    @10
    @33
    @5
    @7
    @10
    wa
    #
    @32
    @2
    @5
    @34
    @29
    @31
    @5
    @7
    @10
    @29
    @28
    @10
    @29
    @28
    @9
    cX
    cP
    c.le
    @5
    @7
    @9
    cX
    wceq
    #
    @5
    cK
    clat
    wcel
    #
    cQ
    cB
    wcel
    #
    @1
    @7
    @35
    wb
    @0
    @36
    @4
    cK
    hllat
    #
    adantr
    #
    @5
    @3
    @37
    @0
    @1
    @2
    @3
    simpr3
    #
    cA
    cB
    cQ
    cK
    cvrat4.b
    cvrat4.a
    atbase
    syl
    #
    @24
    cB
    c.or
    cK
    c.le
    cQ
    cX
    cvrat4.b
    cvrat4.l
    cvrat4.j
    latleeqj2
    syl3anc
    biimpa
    breq2d
    biimpa
    expl
    @5
    @0
    @3
    @2
    @31
    @0
    @4
    simpl
    @40
    @0
    @1
    @2
    @3
    simpr2
    #
    cA
    cQ
    cP
    c.or
    cK
    c.le
    cvrat4.l
    cvrat4.j
    cvrat4.a
    hlatlej2
    syl3anc
    jctird
    @42
    jctild
    impl
    @16
    @32
    vr
    cP
    cA
    @12
    cP
    wceq
    #
    @13
    @29
    @15
    @31
    @12
    cP
    cX
    c.le
    breq1
    @43
    @14
    @30
    cP
    c.le
    @12
    cP
    cQ
    c.or
    oveq2
    breq2d
    anbi12d
    rspcev
    syl
    adantrl
    exp31
    @11
    @10
    @5
    @6
    @7
    wo
    wn
    #
    @17
    @8
    @10
    simpr
    @44
    cP
    cQ
    wne
    #
    @7
    wn
    #
    wa
    #
    @5
    @10
    @17
    wi
    @44
    @6
    wn
    #
    @46
    wa
    @47
    @6
    @7
    ioran
    @45
    @48
    @46
    cP
    cQ
    df-ne
    anbi1i
    bitr4i
    @5
    @47
    @10
    @17
    @5
    @47
    @10
    wa
    #
    cX
    cP
    cQ
    c.or
    co
    #
    cK
    cmee
    cfv
    #
    co
    #
    cA
    wcel
    #
    @52
    cX
    c.le
    wbr
    #
    cP
    cQ
    @52
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    wa
    @17
    @5
    @49
    @53
    @57
    @5
    @45
    @46
    @10
    @53
    @5
    @45
    @46
    @10
    @53
    cA
    cB
    cP
    cQ
    c.or
    cK
    c.le
    @51
    cX
    cvrat4.b
    cvrat4.l
    cvrat4.j
    @51
    eqid
    #
    cvrat4.a
    cvrat3
    3expd
    #
    imp4c
    @5
    @49
    @57
    @5
    @49
    wa
    #
    @54
    @56
    @5
    @54
    @49
    @5
    @36
    @1
    @50
    cB
    wcel
    #
    @54
    @39
    @24
    @5
    @36
    cP
    cB
    wcel
    #
    @37
    @61
    @39
    @5
    @2
    @62
    @42
    cA
    cB
    cP
    cK
    cvrat4.b
    cvrat4.a
    atbase
    syl
    #
    @41
    cB
    c.or
    cK
    cP
    cQ
    cvrat4.b
    cvrat4.j
    latjcl
    syl3anc
    #
    cB
    cK
    c.le
    @51
    cX
    @50
    cvrat4.b
    cvrat4.l
    @58
    latmle1
    syl3anc
    #
    adantr
    @60
    @0
    @53
    @2
    @37
    w3a
    #
    wa
    #
    cQ
    @52
    @51
    co
    #
    c.0
    wceq
    #
    @52
    @30
    c.le
    wbr
    #
    @56
    @60
    @0
    @66
    @0
    @4
    @49
    simpll
    @60
    @53
    @2
    @37
    @5
    @45
    @46
    @10
    @53
    @59
    imp44
    @1
    @2
    @3
    @0
    @49
    simplr2
    @5
    @37
    @49
    @41
    adantr
    3jca
    jca
    @5
    @47
    @69
    @10
    @5
    @46
    @69
    @45
    @5
    @46
    @69
    @5
    @46
    cX
    cQ
    @51
    co
    #
    c.0
    wceq
    #
    @69
    @5
    @46
    cQ
    cX
    @51
    co
    #
    c.0
    wceq
    #
    @72
    @5
    @22
    @3
    @1
    @46
    @74
    wb
    @23
    @40
    @24
    cA
    cB
    cQ
    cK
    c.le
    @51
    cX
    c.0
    cvrat4.b
    cvrat4.l
    @58
    cvrat4.z
    cvrat4.a
    atnle
    syl3anc
    @5
    @73
    @71
    c.0
    @5
    @36
    @37
    @1
    @73
    @71
    wceq
    @39
    @41
    @24
    cB
    cK
    @51
    cQ
    cX
    cvrat4.b
    @58
    latmcom
    syl3anc
    #
    eqeq1d
    bitrd
    @5
    @72
    @68
    c.0
    c.le
    wbr
    #
    @69
    @5
    @68
    @71
    c.le
    wbr
    @72
    @76
    @5
    @68
    @73
    @71
    c.le
    @5
    @36
    @52
    cB
    wcel
    #
    @1
    @37
    w3a
    #
    wa
    @54
    @68
    @73
    c.le
    wbr
    @5
    @36
    @78
    @39
    @5
    @77
    @1
    @37
    @5
    @36
    @1
    @61
    @77
    @39
    @24
    @64
    cB
    cK
    @51
    cX
    @50
    cvrat4.b
    @58
    latmcl
    syl3anc
    #
    @24
    @41
    3jca
    jca
    @65
    cB
    cK
    c.le
    @51
    @52
    cX
    cQ
    cvrat4.b
    cvrat4.l
    @58
    latmlem2
    sylc
    @75
    breqtrd
    @71
    c.0
    @68
    c.le
    breq2
    syl5ibcom
    @5
    cK
    cops
    wcel
    #
    @68
    cB
    wcel
    #
    @76
    @69
    wb
    @0
    @80
    @4
    cK
    hlop
    adantr
    @5
    @36
    @37
    @77
    @81
    @39
    @41
    @79
    cB
    cK
    @51
    cQ
    @52
    cvrat4.b
    @58
    latmcl
    syl3anc
    cB
    cK
    c.le
    @68
    c.0
    cvrat4.b
    cvrat4.l
    cvrat4.z
    ople0
    syl2anc
    sylibd
    sylbid
    imp
    adantrl
    adantrr
    @5
    @70
    @49
    @5
    @52
    @50
    @30
    c.le
    @5
    @36
    @1
    @61
    @52
    @50
    c.le
    wbr
    @39
    @24
    @64
    cB
    cK
    c.le
    @51
    cX
    @50
    cvrat4.b
    cvrat4.l
    @58
    latmle2
    syl3anc
    @5
    @36
    @62
    @37
    @50
    @30
    wceq
    @39
    @63
    @41
    cB
    c.or
    cK
    cP
    cQ
    cvrat4.b
    cvrat4.j
    latjcom
    syl3anc
    breqtrd
    adantr
    @67
    @69
    @52
    cQ
    @51
    co
    #
    c.0
    wceq
    #
    @70
    @56
    wi
    #
    @67
    @68
    @82
    c.0
    @67
    @36
    @37
    @77
    @68
    @82
    wceq
    @0
    @36
    @66
    @38
    adantr
    @0
    @53
    @2
    @37
    simpr3
    @67
    @53
    @77
    @0
    @53
    @2
    @37
    simpr1
    cA
    cB
    @52
    cK
    cvrat4.b
    cvrat4.a
    atbase
    syl
    cB
    cK
    @51
    cQ
    @52
    cvrat4.b
    @58
    latmcom
    syl3anc
    eqeq1d
    @0
    @66
    @83
    @84
    cA
    cB
    @52
    cP
    c.or
    cK
    c.le
    @51
    cQ
    c.0
    cvrat4.b
    cvrat4.l
    cvrat4.j
    @58
    cvrat4.z
    cvrat4.a
    hlexch3
    3expia
    sylbid
    syl3c
    jca
    ex
    jcad
    @16
    @57
    vr
    @52
    cA
    @12
    @52
    wceq
    #
    @13
    @54
    @15
    @56
    @12
    @52
    cX
    c.le
    breq1
    @85
    @14
    @55
    cP
    c.le
    @12
    @52
    cQ
    c.or
    oveq2
    breq2d
    anbi12d
    rspcev
    syl6
    expd
    syl5bi
    syl7
    ecase3d
end
