include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wrex.mm"
include "wa.mm"
include "3dim1.mm"
include "3adant2.mm"
include "wi.mm"
include "wceq.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simp31.mm"
include "necomd.mm"
include "adantr.mm"
include "oveq1.mm"
include "simp11.mm"
include "simp13.mm"
include "hlatjidm.mm"
include "syl2anc.mm"
include "sylan9eqr.mm"
include "breq2d.mm"
include "notbid.mm"
include "wb.mm"
include "cal.mm"
include "hlatl.mm"
include "syl.mm"
include "simp21.mm"
include "atncmp.mm"
include "syl3anc.mm"
include "bitrd.mm"
include "mpbird.mm"
include "simpl32.mm"
include "oveq1d.mm"
include "mtbird.mm"
include "breq1.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "simp22.mm"
include "simp23.mm"
include "jca.mm"
include "ad2antrr.mm"
include "simpll1.mm"
include "simp32.mm"
include "simp33.mm"
include "3jca.mm"
include "simplr.mm"
include "simpr.mm"
include "3dimlem2.mm"
include "3simpc.mm"
include "3expa.mm"
include "ad3antrrr.mm"
include "simp1.mm"
include "simpllr.mm"
include "3dimlem3.mm"
include "syl13anc.mm"
include "3dimlem4.mm"
include "syl121anc.mm"
include "pm2.61dan.mm"
include "pm2.61dane.mm"
include "3exp.mm"
include "3expd.mm"
include "imp32.mm"
include "rexlimdv.mm"
include "rexlimdvva.mm"
include "mpd.mm"

theorem 3dim2
  let cA: class A
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let vs: setvar s
  let vr: setvar r
  let vp: setvar p
  let vq: setvar q
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume 3dim0.j: |- .\/ = ( join ` K )
  assume 3dim0.l: |- .<_ = ( le ` K )
  assume 3dim0.a: |- A = ( Atoms ` K )

  disjoint r s
  disjoint A r
  disjoint A s
  disjoint .\/ r
  disjoint .\/ s
  disjoint .<_ r
  disjoint .<_ s
  disjoint P r
  disjoint P s
  disjoint Q r
  disjoint Q s
  disjoint p q
  disjoint p r
  disjoint p s
  disjoint A p
  disjoint q r
  disjoint q s
  disjoint A q
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint A t
  disjoint u v
  disjoint u w
  disjoint A u
  disjoint v w
  disjoint A v
  disjoint A w
  disjoint q t
  disjoint q u
  disjoint q v
  disjoint q w
  disjoint .\/ q
  disjoint .\/ t
  disjoint .\/ u
  disjoint .\/ v
  disjoint .\/ w
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint .<_ q
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint .<_ t
  disjoint .<_ u
  disjoint .<_ v
  disjoint .<_ w
  disjoint P q
  disjoint P t
  disjoint P u
  disjoint P v
  disjoint P w
  disjoint Q u
  disjoint Q v
  disjoint Q w
  assert |- ( ( K e. HL /\ P e. A /\ Q e. A ) -> E. r e. A E. s e. A ( -. r .<_ ( P .\/ Q ) /\ -. s .<_ ( ( P .\/ Q ) .\/ r ) ) )

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
    cQ
    vu
    cv
    #
    wne
    #
    vv
    cv
    #
    cQ
    @4
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    vw
    cv
    #
    @7
    @6
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    w3a
    #
    vw
    cA
    wrex
    #
    vv
    cA
    wrex
    vu
    cA
    wrex
    #
    vr
    cv
    #
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
    vs
    cv
    #
    @17
    @16
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    wa
    #
    vs
    cA
    wrex
    vr
    cA
    wrex
    #
    @0
    @2
    @15
    @1
    cA
    cQ
    c.or
    cK
    c.le
    vw
    vv
    vu
    3dim0.j
    3dim0.l
    3dim0.a
    3dim1
    3adant2
    @3
    @14
    @25
    vu
    vv
    cA
    cA
    @3
    @4
    cA
    wcel
    #
    @6
    cA
    wcel
    #
    wa
    #
    wa
    @13
    @25
    vw
    cA
    @3
    @26
    @27
    @10
    cA
    wcel
    #
    @13
    @25
    wi
    #
    wi
    @3
    @26
    @27
    @29
    @30
    @3
    @26
    @27
    @29
    w3a
    #
    @13
    @25
    @3
    @31
    @13
    w3a
    #
    @25
    cP
    cQ
    @32
    cP
    cQ
    wceq
    #
    wa
    #
    @26
    @27
    @4
    @17
    c.le
    wbr
    #
    wn
    #
    @6
    @17
    @4
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    @25
    @26
    @27
    @29
    @3
    @13
    @33
    simpl21
    @26
    @27
    @29
    @3
    @13
    @33
    simpl22
    @34
    @36
    @4
    cQ
    wne
    #
    @32
    @40
    @33
    @32
    cQ
    @4
    @3
    @31
    @5
    @9
    @12
    simp31
    #
    necomd
    adantr
    @34
    @36
    @4
    cQ
    c.le
    wbr
    #
    wn
    #
    @40
    @34
    @35
    @42
    @34
    @17
    cQ
    @4
    c.le
    @33
    @32
    @17
    cQ
    cQ
    c.or
    co
    #
    cQ
    cP
    cQ
    cQ
    c.or
    oveq1
    @32
    @0
    @2
    @44
    cQ
    wceq
    @0
    @1
    @2
    @31
    @13
    simp11
    #
    @0
    @1
    @2
    @31
    @13
    simp13
    #
    cA
    c.or
    cK
    cQ
    3dim0.j
    3dim0.a
    hlatjidm
    syl2anc
    sylan9eqr
    #
    breq2d
    notbid
    @32
    @43
    @40
    wb
    #
    @33
    @32
    cK
    cal
    wcel
    #
    @26
    @2
    @48
    @32
    @0
    @49
    @45
    cK
    hlatl
    syl
    @3
    @26
    @27
    @29
    @13
    simp21
    #
    @46
    cA
    @4
    cQ
    cK
    c.le
    3dim0.l
    3dim0.a
    atncmp
    syl3anc
    adantr
    bitrd
    mpbird
    @34
    @38
    @8
    @5
    @9
    @12
    @3
    @31
    @33
    simpl32
    @34
    @37
    @7
    @6
    c.le
    @34
    @17
    cQ
    @4
    c.or
    @47
    oveq1d
    breq2d
    mtbird
    @24
    @36
    @39
    wa
    #
    @36
    @20
    @37
    c.le
    wbr
    #
    wn
    #
    wa
    #
    vr
    vs
    @4
    @6
    cA
    cA
    @16
    @4
    wceq
    #
    @19
    @36
    @23
    @53
    @55
    @18
    @35
    @16
    @4
    @17
    c.le
    breq1
    notbid
    @55
    @22
    @52
    @55
    @21
    @37
    @20
    c.le
    @16
    @4
    @17
    c.or
    oveq2
    breq2d
    notbid
    anbi12d
    #
    @20
    @6
    wceq
    #
    @53
    @39
    @36
    @57
    @52
    @38
    @20
    @6
    @37
    c.le
    breq1
    notbid
    anbi2d
    rspc2ev
    #
    syl112anc
    @32
    cP
    cQ
    wne
    #
    wa
    #
    cP
    @7
    c.le
    wbr
    #
    @25
    @60
    @61
    wa
    #
    @27
    @29
    wa
    #
    @6
    @17
    c.le
    wbr
    #
    wn
    #
    @10
    @17
    @6
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    wa
    #
    @25
    @32
    @63
    @59
    @61
    @32
    @27
    @29
    @3
    @26
    @27
    @29
    @13
    simp22
    #
    @3
    @26
    @27
    @29
    @13
    simp23
    #
    jca
    ad2antrr
    @62
    @59
    @65
    @68
    w3a
    #
    @69
    @62
    @3
    @26
    @9
    @12
    w3a
    #
    @59
    @61
    @72
    @3
    @31
    @13
    @59
    @61
    simpll1
    @32
    @73
    @59
    @61
    @32
    @26
    @9
    @12
    @50
    @3
    @31
    @5
    @9
    @12
    simp32
    #
    @3
    @31
    @5
    @9
    @12
    simp33
    #
    3jca
    ad2antrr
    @32
    @59
    @61
    simplr
    @60
    @61
    simpr
    cA
    cP
    cQ
    @4
    @6
    @10
    c.or
    cK
    c.le
    3dim0.j
    3dim0.l
    3dim0.a
    3dimlem2
    syl112anc
    @59
    @65
    @68
    3simpc
    syl
    @27
    @29
    @69
    @25
    @24
    @69
    @65
    @20
    @66
    c.le
    wbr
    #
    wn
    #
    wa
    vr
    vs
    @6
    @10
    cA
    cA
    @16
    @6
    wceq
    #
    @19
    @65
    @23
    @77
    @78
    @18
    @64
    @16
    @6
    @17
    c.le
    breq1
    notbid
    @78
    @22
    @76
    @78
    @21
    @66
    @20
    c.le
    @16
    @6
    @17
    c.or
    oveq2
    breq2d
    notbid
    anbi12d
    @20
    @10
    wceq
    #
    @77
    @68
    @65
    @79
    @76
    @67
    @20
    @10
    @66
    c.le
    breq1
    notbid
    anbi2d
    rspc2ev
    3expa
    syl2anc
    @60
    @61
    wn
    #
    wa
    #
    cP
    @11
    c.le
    wbr
    #
    @25
    @81
    @82
    wa
    #
    @26
    @29
    wa
    #
    @36
    @10
    @37
    c.le
    wbr
    #
    wn
    #
    wa
    #
    @25
    @32
    @84
    @59
    @80
    @82
    @32
    @26
    @29
    @50
    @71
    jca
    ad3antrrr
    @83
    @59
    @36
    @86
    w3a
    #
    @87
    @83
    @3
    @28
    @5
    @12
    wa
    #
    w3a
    #
    @59
    @80
    @82
    @88
    @32
    @90
    @59
    @80
    @82
    @32
    @3
    @28
    @89
    @3
    @31
    @13
    simp1
    #
    @32
    @26
    @27
    @50
    @70
    jca
    #
    @32
    @5
    @12
    @41
    @75
    jca
    3jca
    ad3antrrr
    @32
    @59
    @80
    @82
    simpllr
    @60
    @80
    @82
    simplr
    @81
    @82
    simpr
    cA
    cP
    cQ
    @4
    @6
    @10
    c.or
    cK
    c.le
    3dim0.j
    3dim0.l
    3dim0.a
    3dimlem3
    syl13anc
    @59
    @36
    @86
    3simpc
    syl
    @26
    @29
    @87
    @25
    @24
    @87
    @54
    vr
    vs
    @4
    @10
    cA
    cA
    @56
    @79
    @53
    @86
    @36
    @79
    @52
    @85
    @20
    @10
    @37
    c.le
    breq1
    notbid
    anbi2d
    rspc2ev
    3expa
    syl2anc
    @81
    @82
    wn
    #
    wa
    #
    @28
    @51
    @25
    @32
    @28
    @59
    @80
    @93
    @92
    ad3antrrr
    @94
    @59
    @36
    @39
    w3a
    #
    @51
    @94
    @3
    @28
    @5
    @9
    wa
    #
    w3a
    #
    @59
    @80
    @93
    @95
    @32
    @97
    @59
    @80
    @93
    @32
    @3
    @28
    @96
    @91
    @92
    @32
    @5
    @9
    @41
    @74
    jca
    3jca
    ad3antrrr
    @32
    @59
    @80
    @93
    simpllr
    @60
    @80
    @93
    simplr
    @81
    @93
    simpr
    cA
    cP
    cQ
    @4
    @6
    c.or
    cK
    c.le
    3dim0.j
    3dim0.l
    3dim0.a
    3dimlem4
    syl121anc
    @59
    @36
    @39
    3simpc
    syl
    @26
    @27
    @51
    @25
    @58
    3expa
    syl2anc
    pm2.61dan
    pm2.61dan
    pm2.61dane
    3exp
    3expd
    imp32
    rexlimdv
    rexlimdvva
    mpd
end
