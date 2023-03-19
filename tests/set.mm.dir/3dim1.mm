include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wrex.mm"
include "3dim0.mm"
include "adantr.mm"
include "wi.mm"
include "wceq.mm"
include "simpl2.mm"
include "3dimlem1.mm"
include "3ad2antl3.mm"
include "3dim1lem5.mm"
include "syl2anc.mm"
include "simp13.mm"
include "simp22.mm"
include "simp23.mm"
include "3jca.mm"
include "ad2antrr.mm"
include "simpll1.mm"
include "simp21.mm"
include "simp32.mm"
include "simp33.mm"
include "simplr.mm"
include "simpr.mm"
include "3dimlem2.mm"
include "syl112anc.mm"
include "simp1.mm"
include "jca.mm"
include "simp31.mm"
include "simplrl.mm"
include "simplrr.mm"
include "3dimlem3.mm"
include "syl13anc.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpl31.mm"
include "simpl32.mm"
include "3dimlem4.mm"
include "syl3anc.mm"
include "pm2.61dan.mm"
include "anassrs.mm"
include "pm2.61dane.mm"
include "3exp.mm"
include "3expd.mm"
include "imp43.mm"
include "impd.mm"
include "rexlimdvv.mm"
include "rexlimdvva.mm"
include "mpd.mm"

theorem 3dim1
  let cA: class A
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume 3dim0.j: |- .\/ = ( join ` K )
  assume 3dim0.l: |- .<_ = ( le ` K )
  assume 3dim0.a: |- A = ( Atoms ` K )

  disjoint q r
  disjoint q s
  disjoint A q
  disjoint r s
  disjoint A r
  disjoint A s
  disjoint .\/ r
  disjoint .\/ s
  disjoint .\/ q
  disjoint .<_ q
  disjoint .<_ r
  disjoint .<_ s
  disjoint P q
  disjoint P r
  disjoint P s
  disjoint p q
  disjoint p r
  disjoint p s
  disjoint A p
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
  disjoint .\/ t
  disjoint .\/ u
  disjoint .\/ v
  disjoint .\/ w
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K w
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
  disjoint P t
  disjoint P u
  disjoint P v
  disjoint P w
  assert |- ( ( K e. HL /\ P e. A ) -> E. q e. A E. r e. A E. s e. A ( P =/= q /\ -. r .<_ ( P .\/ q ) /\ -. s .<_ ( ( P .\/ q ) .\/ r ) ) )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    wa
    #
    vt
    cv
    #
    vu
    cv
    #
    wne
    #
    vv
    cv
    #
    @3
    @4
    c.or
    co
    #
    c.le
    wbr
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
    vv
    cA
    wrex
    #
    vu
    cA
    wrex
    vt
    cA
    wrex
    #
    cP
    vq
    cv
    #
    wne
    vr
    cv
    #
    cP
    @15
    c.or
    co
    #
    c.le
    wbr
    wn
    vs
    cv
    @17
    @16
    c.or
    co
    c.le
    wbr
    wn
    w3a
    vs
    cA
    wrex
    vr
    cA
    wrex
    vq
    cA
    wrex
    #
    @0
    @14
    @1
    cA
    c.or
    cK
    c.le
    vw
    vv
    vu
    vt
    3dim0.j
    3dim0.l
    3dim0.a
    3dim0
    adantr
    @2
    @13
    @18
    vt
    vu
    cA
    cA
    @2
    @3
    cA
    wcel
    #
    @4
    cA
    wcel
    #
    wa
    wa
    #
    @12
    @18
    vv
    vw
    cA
    cA
    @21
    @6
    cA
    wcel
    #
    @9
    cA
    wcel
    #
    @12
    @18
    wi
    #
    @0
    @1
    @19
    @20
    @22
    @23
    @24
    wi
    wi
    #
    @0
    @1
    @19
    @20
    @25
    wi
    @0
    @1
    @19
    w3a
    #
    @20
    @22
    @23
    @24
    @26
    @20
    @22
    @23
    w3a
    #
    @12
    @18
    @26
    @27
    @12
    w3a
    #
    @18
    cP
    @3
    @28
    cP
    @3
    wceq
    #
    wa
    @27
    cP
    @4
    wne
    @6
    cP
    @4
    c.or
    co
    #
    c.le
    wbr
    wn
    @9
    @30
    @6
    c.or
    co
    c.le
    wbr
    wn
    w3a
    #
    @18
    @26
    @27
    @12
    @29
    simpl2
    @12
    @26
    @29
    @31
    @27
    cA
    cP
    @3
    @4
    @6
    @9
    c.or
    cK
    c.le
    3dim0.j
    3dim0.l
    3dim0.a
    3dimlem1
    3ad2antl3
    vw
    vv
    vu
    cA
    cP
    c.or
    cK
    c.le
    vs
    vr
    vq
    3dim0.j
    3dim0.l
    3dim0.a
    3dim1lem5
    syl2anc
    @28
    cP
    @3
    wne
    #
    wa
    #
    cP
    @7
    c.le
    wbr
    #
    @18
    @33
    @34
    wa
    #
    @19
    @22
    @23
    w3a
    #
    @32
    @6
    cP
    @3
    c.or
    co
    #
    c.le
    wbr
    wn
    @9
    @37
    @6
    c.or
    co
    c.le
    wbr
    wn
    w3a
    #
    @18
    @28
    @36
    @32
    @34
    @28
    @19
    @22
    @23
    @0
    @1
    @19
    @27
    @12
    simp13
    #
    @26
    @20
    @22
    @23
    @12
    simp22
    #
    @26
    @20
    @22
    @23
    @12
    simp23
    #
    3jca
    ad2antrr
    @35
    @26
    @20
    @8
    @11
    w3a
    #
    @32
    @34
    @38
    @26
    @27
    @12
    @32
    @34
    simpll1
    @28
    @42
    @32
    @34
    @28
    @20
    @8
    @11
    @26
    @20
    @22
    @23
    @12
    simp21
    #
    @26
    @27
    @5
    @8
    @11
    simp32
    @26
    @27
    @5
    @8
    @11
    simp33
    #
    3jca
    ad2antrr
    @28
    @32
    @34
    simplr
    @33
    @34
    simpr
    cA
    cP
    @3
    @4
    @6
    @9
    c.or
    cK
    c.le
    3dim0.j
    3dim0.l
    3dim0.a
    3dimlem2
    syl112anc
    vw
    vv
    vt
    cA
    cP
    c.or
    cK
    c.le
    vs
    vr
    vq
    3dim0.j
    3dim0.l
    3dim0.a
    3dim1lem5
    syl2anc
    @28
    @32
    @34
    wn
    #
    @18
    @28
    @32
    @45
    wa
    #
    wa
    #
    cP
    @10
    c.le
    wbr
    #
    @18
    @47
    @48
    wa
    #
    @19
    @20
    @23
    w3a
    #
    @32
    @4
    @37
    c.le
    wbr
    wn
    #
    @9
    @37
    @4
    c.or
    co
    #
    c.le
    wbr
    wn
    w3a
    #
    @18
    @28
    @50
    @46
    @48
    @28
    @19
    @20
    @23
    @39
    @43
    @41
    3jca
    ad2antrr
    @49
    @26
    @20
    @22
    wa
    #
    @5
    @11
    wa
    #
    w3a
    #
    @32
    @45
    @48
    @53
    @28
    @56
    @46
    @48
    @28
    @26
    @54
    @55
    @26
    @27
    @12
    simp1
    @28
    @20
    @22
    @43
    @40
    jca
    @28
    @5
    @11
    @26
    @27
    @5
    @8
    @11
    simp31
    @44
    jca
    3jca
    ad2antrr
    @28
    @32
    @45
    @48
    simplrl
    @28
    @32
    @45
    @48
    simplrr
    @47
    @48
    simpr
    cA
    cP
    @3
    @4
    @6
    @9
    c.or
    cK
    c.le
    3dim0.j
    3dim0.l
    3dim0.a
    3dimlem3
    syl13anc
    vw
    vu
    vt
    cA
    cP
    c.or
    cK
    c.le
    vs
    vr
    vq
    3dim0.j
    3dim0.l
    3dim0.a
    3dim1lem5
    syl2anc
    @47
    @48
    wn
    #
    wa
    #
    @19
    @20
    @22
    w3a
    #
    @32
    @51
    @6
    @52
    c.le
    wbr
    wn
    w3a
    #
    @18
    @28
    @59
    @46
    @57
    @28
    @19
    @20
    @22
    @39
    @43
    @40
    3jca
    ad2antrr
    @58
    @26
    @54
    @5
    @8
    wa
    #
    w3a
    #
    @46
    @57
    @60
    @47
    @62
    @57
    @47
    @26
    @54
    @61
    @26
    @27
    @12
    @46
    simpl1
    @47
    @20
    @22
    @20
    @22
    @23
    @26
    @12
    @46
    simpl21
    @20
    @22
    @23
    @26
    @12
    @46
    simpl22
    jca
    @47
    @5
    @8
    @5
    @8
    @11
    @26
    @27
    @46
    simpl31
    @5
    @8
    @11
    @26
    @27
    @46
    simpl32
    jca
    3jca
    adantr
    @28
    @46
    @57
    simplr
    @47
    @57
    simpr
    cA
    cP
    @3
    @4
    @6
    c.or
    cK
    c.le
    3dim0.j
    3dim0.l
    3dim0.a
    3dimlem4
    syl3anc
    vv
    vu
    vt
    cA
    cP
    c.or
    cK
    c.le
    vs
    vr
    vq
    3dim0.j
    3dim0.l
    3dim0.a
    3dim1lem5
    syl2anc
    pm2.61dan
    anassrs
    pm2.61dan
    pm2.61dane
    3exp
    3expd
    3exp
    imp43
    impd
    rexlimdvv
    rexlimdvva
    mpd
end
