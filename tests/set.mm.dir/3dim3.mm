include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wrex.mm"
include "3dim2.mm"
include "3adant3r1.mm"
include "wceq.mm"
include "simpl2l.mm"
include "simp3l.mm"
include "simp1l.mm"
include "simp1r2.mm"
include "hlatjidm.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "mtbird.mm"
include "oveq1.mm"
include "notbid.mm"
include "biimparc.mm"
include "sylan.mm"
include "breq1.mm"
include "rspcev.mm"
include "wne.mm"
include "simp2l.mm"
include "ad2antrr.mm"
include "hlatjass.mm"
include "3ad2ant1.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "hllat.mm"
include "syl.mm"
include "simp1r1.mm"
include "eqid.mm"
include "atbase.mm"
include "simp1r3.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "3jca.mm"
include "adantr.mm"
include "latleeqj1.mm"
include "biimpa.mm"
include "eqtrd.mm"
include "simpl2r.mm"
include "ad3antrrr.mm"
include "jca.mm"
include "simpl3r.mm"
include "simplr.mm"
include "simpr.mm"
include "3dimlem3a.mm"
include "syl113anc.mm"
include "simpl3l.mm"
include "3dimlem4a.mm"
include "pm2.61dan.mm"
include "pm2.61dane.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "mpd.mm"

theorem 3dim3
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let vs: setvar s
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume 3dim0.j: |- .\/ = ( join ` K )
  assume 3dim0.l: |- .<_ = ( le ` K )
  assume 3dim0.a: |- A = ( Atoms ` K )

  disjoint A s
  disjoint .\/ s
  disjoint .<_ s
  disjoint P s
  disjoint Q s
  disjoint R s
  disjoint p q
  disjoint p r
  disjoint p s
  disjoint A p
  disjoint q r
  disjoint q s
  disjoint A q
  disjoint r s
  disjoint A r
  disjoint .\/ r
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
  disjoint .<_ r
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint .<_ t
  disjoint .<_ u
  disjoint .<_ v
  disjoint .<_ w
  disjoint P q
  disjoint P r
  disjoint P t
  disjoint P u
  disjoint P v
  disjoint P w
  disjoint Q r
  disjoint Q u
  disjoint Q v
  disjoint Q w
  disjoint R v
  disjoint R w
  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) ) -> E. s e. A -. s .<_ ( ( P .\/ Q ) .\/ R ) )

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
    cR
    cA
    wcel
    #
    w3a
    #
    wa
    #
    vv
    cv
    #
    cQ
    cR
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
    wa
    #
    vw
    cA
    wrex
    vv
    cA
    wrex
    #
    vs
    cv
    #
    cP
    cQ
    c.or
    co
    #
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    vs
    cA
    wrex
    #
    @0
    @2
    @3
    @14
    @1
    cA
    cQ
    cR
    c.or
    cK
    c.le
    vw
    vv
    3dim0.j
    3dim0.l
    3dim0.a
    3dim2
    3adant3r1
    @5
    @13
    @20
    vv
    vw
    cA
    cA
    @5
    @6
    cA
    wcel
    #
    @10
    cA
    wcel
    #
    wa
    #
    @13
    @20
    @5
    @23
    @13
    w3a
    #
    @20
    cP
    cQ
    @24
    cP
    cQ
    wceq
    #
    wa
    @21
    @6
    @17
    c.le
    wbr
    #
    wn
    #
    @20
    @21
    @22
    @5
    @13
    @25
    simpl2l
    @24
    @6
    cQ
    cQ
    c.or
    co
    #
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    @25
    @27
    @24
    @30
    @8
    @5
    @23
    @9
    @12
    simp3l
    #
    @24
    @29
    @7
    @6
    c.le
    @24
    @28
    cQ
    cR
    c.or
    @24
    @0
    @2
    @28
    cQ
    wceq
    @0
    @4
    @23
    @13
    simp1l
    #
    @1
    @2
    @3
    @0
    @23
    @13
    simp1r2
    #
    cA
    c.or
    cK
    cQ
    3dim0.j
    3dim0.a
    hlatjidm
    syl2anc
    oveq1d
    breq2d
    mtbird
    @25
    @27
    @31
    @25
    @26
    @30
    @25
    @17
    @29
    @6
    c.le
    @25
    @16
    @28
    cR
    c.or
    cP
    cQ
    cQ
    c.or
    oveq1
    oveq1d
    breq2d
    notbid
    biimparc
    sylan
    @19
    @27
    vs
    @6
    cA
    @15
    @6
    wceq
    @18
    @26
    @15
    @6
    @17
    c.le
    breq1
    notbid
    rspcev
    #
    syl2anc
    @24
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
    @20
    @37
    @38
    wa
    #
    @21
    @27
    @20
    @24
    @21
    @36
    @38
    @5
    @21
    @22
    @13
    simp2l
    #
    ad2antrr
    @39
    @26
    @8
    @24
    @9
    @36
    @38
    @32
    ad2antrr
    @39
    @17
    @7
    @6
    c.le
    @39
    @17
    cP
    @7
    c.or
    co
    #
    @7
    @24
    @17
    @41
    wceq
    #
    @36
    @38
    @5
    @23
    @42
    @13
    cA
    cP
    cQ
    cR
    c.or
    cK
    3dim0.j
    3dim0.a
    hlatjass
    3ad2ant1
    ad2antrr
    @37
    @38
    @41
    @7
    wceq
    #
    @37
    cK
    clat
    wcel
    #
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    @7
    @45
    wcel
    #
    w3a
    #
    @38
    @43
    wb
    @24
    @48
    @36
    @24
    @44
    @46
    @47
    @24
    @0
    @44
    @33
    cK
    hllat
    syl
    @24
    @1
    @46
    @1
    @2
    @3
    @0
    @23
    @13
    simp1r1
    #
    cA
    @45
    cP
    cK
    @45
    eqid
    #
    3dim0.a
    atbase
    syl
    @24
    @0
    @2
    @3
    @47
    @33
    @34
    @1
    @2
    @3
    @0
    @23
    @13
    simp1r3
    #
    cA
    @45
    c.or
    cK
    cQ
    cR
    @50
    3dim0.j
    3dim0.a
    hlatjcl
    syl3anc
    3jca
    adantr
    @45
    c.or
    cK
    c.le
    cP
    @7
    @50
    3dim0.l
    3dim0.j
    latleeqj1
    syl
    biimpa
    eqtrd
    breq2d
    mtbird
    @35
    syl2anc
    @37
    @38
    wn
    #
    wa
    #
    cP
    @11
    c.le
    wbr
    #
    @20
    @53
    @54
    wa
    #
    @22
    @10
    @17
    c.le
    wbr
    #
    wn
    #
    @20
    @37
    @22
    @52
    @54
    @21
    @22
    @5
    @13
    @36
    simpl2r
    ad2antrr
    @55
    @0
    @1
    @2
    w3a
    #
    @3
    @21
    wa
    #
    @12
    @52
    @54
    @57
    @24
    @58
    @36
    @52
    @54
    @24
    @0
    @1
    @2
    @33
    @49
    @34
    3jca
    #
    ad3antrrr
    @24
    @59
    @36
    @52
    @54
    @24
    @3
    @21
    @51
    @40
    jca
    #
    ad3antrrr
    @37
    @12
    @52
    @54
    @9
    @12
    @5
    @23
    @36
    simpl3r
    ad2antrr
    @37
    @52
    @54
    simplr
    @53
    @54
    simpr
    cA
    cP
    cQ
    cR
    @6
    @10
    c.or
    cK
    c.le
    3dim0.j
    3dim0.l
    3dim0.a
    3dimlem3a
    syl113anc
    @19
    @57
    vs
    @10
    cA
    @15
    @10
    wceq
    @18
    @56
    @15
    @10
    @17
    c.le
    breq1
    notbid
    rspcev
    syl2anc
    @53
    @54
    wn
    #
    wa
    #
    @21
    @27
    @20
    @37
    @21
    @52
    @62
    @21
    @22
    @5
    @13
    @36
    simpl2l
    ad2antrr
    @63
    @58
    @59
    @9
    @52
    @62
    @27
    @24
    @58
    @36
    @52
    @62
    @60
    ad3antrrr
    @24
    @59
    @36
    @52
    @62
    @61
    ad3antrrr
    @37
    @9
    @52
    @62
    @9
    @12
    @5
    @23
    @36
    simpl3l
    ad2antrr
    @37
    @52
    @62
    simplr
    @53
    @62
    simpr
    cA
    cP
    cQ
    cR
    @6
    c.or
    cK
    c.le
    3dim0.j
    3dim0.l
    3dim0.a
    3dimlem4a
    syl113anc
    @35
    syl2anc
    pm2.61dan
    pm2.61dan
    pm2.61dane
    3exp
    rexlimdvv
    mpd
end
