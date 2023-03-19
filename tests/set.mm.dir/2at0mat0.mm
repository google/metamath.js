include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wceq.mm"
include "wo.mm"
include "co.mm"
include "wne.mm"
include "wa.mm"
include "simpll.mm"
include "simplr1.mm"
include "simpr.mm"
include "simplr3.mm"
include "col.mm"
include "cbs.mm"
include "cfv.mm"
include "simpl1.mm"
include "hlol.mm"
include "syl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simpl3.mm"
include "meetat2.mm"
include "adantr.mm"
include "oveq1.mm"
include "hlatjidm.mm"
include "syl2anc.mm"
include "sylan9eqr.mm"
include "oveq1d.mm"
include "clat.mm"
include "hllat.mm"
include "atbase.mm"
include "latmcom.mm"
include "eqtrd.mm"
include "eleq1d.mm"
include "eqeq1d.mm"
include "orbi12d.mm"
include "mpbird.mm"
include "oveq2d.mm"
include "adantlr.mm"
include "wn.mm"
include "df-ne.mm"
include "wi.mm"
include "clln.mm"
include "simpll1.mm"
include "simpll2.mm"
include "simpll3.mm"
include "llni2.mm"
include "syl31anc.mm"
include "simplr2.mm"
include "simpr3.mm"
include "2llnmat.mm"
include "syl32anc.mm"
include "3exp2.mm"
include "imp31.mm"
include "syl5bir.mm"
include "orrd.mm"
include "orcomd.mm"
include "pm2.61dane.mm"
include "syl13anc.mm"
include "oveq2.mm"
include "olj01.mm"
include "mpjaodan.mm"

theorem 2at0mat0
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let c.0: class .0.
  assume 2atmatz.j: |- .\/ = ( join ` K )
  assume 2atmatz.m: |- ./\ = ( meet ` K )
  assume 2atmatz.z: |- .0. = ( 0. ` K )
  assume 2atmatz.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ ( S e. A \/ S = .0. ) /\ ( P .\/ Q ) =/= ( R .\/ S ) ) ) -> ( ( ( P .\/ Q ) ./\ ( R .\/ S ) ) e. A \/ ( ( P .\/ Q ) ./\ ( R .\/ S ) ) = .0. ) )

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
    cR
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    cS
    c.0
    wceq
    #
    wo
    #
    cP
    cQ
    c.or
    co
    #
    cR
    cS
    c.or
    co
    #
    wne
    #
    w3a
    #
    wa
    #
    @5
    @8
    @9
    c.an
    co
    #
    cA
    wcel
    #
    @13
    c.0
    wceq
    #
    wo
    #
    @6
    @12
    @5
    wa
    @3
    @4
    @5
    @10
    @16
    @3
    @11
    @5
    simpll
    @4
    @7
    @10
    @3
    @5
    simplr1
    @12
    @5
    simpr
    @4
    @7
    @10
    @3
    @5
    simplr3
    @3
    @4
    @5
    @10
    w3a
    #
    wa
    #
    @16
    cP
    cQ
    @18
    cP
    cQ
    wceq
    #
    wa
    #
    @16
    @9
    cQ
    c.an
    co
    #
    cA
    wcel
    #
    @21
    c.0
    wceq
    #
    wo
    #
    @18
    @24
    @19
    @18
    cK
    col
    wcel
    #
    @9
    cK
    cbs
    cfv
    #
    wcel
    #
    @2
    @24
    @18
    @0
    @25
    @0
    @1
    @2
    @17
    simpl1
    #
    cK
    hlol
    #
    syl
    #
    @18
    @0
    @4
    @5
    @27
    @28
    @3
    @4
    @5
    @10
    simpr1
    @3
    @4
    @5
    @10
    simpr2
    #
    cA
    @26
    c.or
    cK
    cR
    cS
    @26
    eqid
    #
    2atmatz.j
    2atmatz.a
    hlatjcl
    syl3anc
    #
    @0
    @1
    @2
    @17
    simpl3
    #
    cA
    @26
    cQ
    cK
    c.an
    @9
    c.0
    @32
    2atmatz.m
    2atmatz.z
    2atmatz.a
    meetat2
    syl3anc
    adantr
    @20
    @14
    @22
    @15
    @23
    @20
    @13
    @21
    cA
    @20
    @13
    cQ
    @9
    c.an
    co
    #
    @21
    @20
    @8
    cQ
    @9
    c.an
    @19
    @18
    @8
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
    @18
    @0
    @2
    @36
    cQ
    wceq
    @28
    @34
    cA
    c.or
    cK
    cQ
    2atmatz.j
    2atmatz.a
    hlatjidm
    syl2anc
    sylan9eqr
    oveq1d
    @18
    @35
    @21
    wceq
    #
    @19
    @18
    cK
    clat
    wcel
    #
    cQ
    @26
    wcel
    #
    @27
    @37
    @18
    @0
    @38
    @28
    cK
    hllat
    syl
    @18
    @2
    @39
    @34
    cA
    @26
    cQ
    cK
    @32
    2atmatz.a
    atbase
    syl
    @33
    @26
    cK
    c.an
    cQ
    @9
    @32
    2atmatz.m
    latmcom
    syl3anc
    adantr
    eqtrd
    #
    eleq1d
    @20
    @13
    @21
    c.0
    @40
    eqeq1d
    orbi12d
    mpbird
    @18
    cP
    cQ
    wne
    #
    wa
    #
    @16
    cR
    cS
    @18
    cR
    cS
    wceq
    #
    @16
    @41
    @18
    @43
    wa
    #
    @16
    @8
    cS
    c.an
    co
    #
    cA
    wcel
    #
    @45
    c.0
    wceq
    #
    wo
    #
    @18
    @48
    @43
    @18
    @25
    @8
    @26
    wcel
    #
    @5
    @48
    @30
    @3
    @49
    @17
    cA
    @26
    c.or
    cK
    cP
    cQ
    @32
    2atmatz.j
    2atmatz.a
    hlatjcl
    #
    adantr
    @31
    cA
    @26
    cS
    cK
    c.an
    @8
    c.0
    @32
    2atmatz.m
    2atmatz.z
    2atmatz.a
    meetat2
    syl3anc
    adantr
    @44
    @14
    @46
    @15
    @47
    @44
    @13
    @45
    cA
    @44
    @9
    cS
    @8
    c.an
    @43
    @18
    @9
    cS
    cS
    c.or
    co
    #
    cS
    cR
    cS
    cS
    c.or
    oveq1
    @18
    @0
    @5
    @51
    cS
    wceq
    @28
    @31
    cA
    c.or
    cK
    cS
    2atmatz.j
    2atmatz.a
    hlatjidm
    syl2anc
    sylan9eqr
    oveq2d
    #
    eleq1d
    @44
    @13
    @45
    c.0
    @52
    eqeq1d
    orbi12d
    mpbird
    adantlr
    @42
    cR
    cS
    wne
    #
    wa
    #
    @15
    @14
    @54
    @15
    @14
    @15
    wn
    @13
    c.0
    wne
    #
    @54
    @14
    @13
    c.0
    df-ne
    @18
    @41
    @53
    @55
    @14
    wi
    @18
    @41
    @53
    @55
    @14
    @18
    @41
    @53
    @55
    w3a
    #
    wa
    #
    @0
    @8
    cK
    clln
    cfv
    #
    wcel
    #
    @9
    @58
    wcel
    #
    @10
    @55
    @14
    @0
    @1
    @2
    @17
    @56
    simpll1
    #
    @57
    @0
    @1
    @2
    @41
    @59
    @61
    @0
    @1
    @2
    @17
    @56
    simpll2
    @0
    @1
    @2
    @17
    @56
    simpll3
    @18
    @41
    @53
    @55
    simpr1
    cA
    cP
    cQ
    c.or
    cK
    @58
    2atmatz.j
    2atmatz.a
    @58
    eqid
    #
    llni2
    syl31anc
    @57
    @0
    @4
    @5
    @53
    @60
    @61
    @4
    @5
    @10
    @3
    @56
    simplr1
    @4
    @5
    @10
    @3
    @56
    simplr2
    @18
    @41
    @53
    @55
    simpr2
    cA
    cR
    cS
    c.or
    cK
    @58
    2atmatz.j
    2atmatz.a
    @62
    llni2
    syl31anc
    @4
    @5
    @10
    @3
    @56
    simplr3
    @18
    @41
    @53
    @55
    simpr3
    cA
    cK
    c.an
    @58
    @8
    @9
    c.0
    2atmatz.m
    2atmatz.z
    2atmatz.a
    @62
    2llnmat
    syl32anc
    3exp2
    imp31
    syl5bir
    orrd
    orcomd
    pm2.61dane
    pm2.61dane
    syl13anc
    @12
    @6
    wa
    #
    @16
    @8
    cR
    c.an
    co
    #
    cA
    wcel
    #
    @64
    c.0
    wceq
    #
    wo
    #
    @12
    @67
    @6
    @12
    @25
    @49
    @4
    @67
    @12
    @0
    @25
    @0
    @1
    @2
    @11
    simpl1
    @29
    syl
    #
    @3
    @49
    @11
    @50
    adantr
    @3
    @4
    @7
    @10
    simpr1
    #
    cA
    @26
    cR
    cK
    c.an
    @8
    c.0
    @32
    2atmatz.m
    2atmatz.z
    2atmatz.a
    meetat2
    syl3anc
    adantr
    @63
    @14
    @65
    @15
    @66
    @63
    @13
    @64
    cA
    @63
    @9
    cR
    @8
    c.an
    @6
    @12
    @9
    cR
    c.0
    c.or
    co
    #
    cR
    cS
    c.0
    cR
    c.or
    oveq2
    @12
    @25
    cR
    @26
    wcel
    #
    @70
    cR
    wceq
    @68
    @12
    @4
    @71
    @69
    cA
    @26
    cR
    cK
    @32
    2atmatz.a
    atbase
    syl
    @26
    c.or
    cK
    cR
    c.0
    @32
    2atmatz.j
    2atmatz.z
    olj01
    syl2anc
    sylan9eqr
    oveq2d
    #
    eleq1d
    @63
    @13
    @64
    c.0
    @72
    eqeq1d
    orbi12d
    mpbird
    @3
    @4
    @7
    @10
    simpr2
    mpjaodan
end
