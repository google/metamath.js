include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cp0.mm"
include "wa.mm"
include "c0.mm"
include "wss.mm"
include "simp1.mm"
include "atbase.mm"
include "3ad2ant3.mm"
include "pmapssat.mm"
include "syl2anc.mm"
include "padd02.mm"
include "adantr.mm"
include "fveq2.mm"
include "cal.mm"
include "hlatl.mm"
include "3ad2ant1.mm"
include "eqid.mm"
include "pmap0.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "col.mm"
include "hlol.mm"
include "olj02.mm"
include "fveq2d.mm"
include "3eqtr4rd.mm"
include "wne.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wrex.mm"
include "simpll1.mm"
include "simpll2.mm"
include "simplr.mm"
include "simpll3.mm"
include "3jca.mm"
include "simpllr.mm"
include "simpr.mm"
include "cvrat42.mm"
include "imp.mm"
include "syl22anc.mm"
include "ex.mm"
include "wb.mm"
include "elpmap.mm"
include "3adant3.mm"
include "wex.mm"
include "df-rex.mm"
include "elpmapat.mm"
include "3adant2.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "syl5rbb.mm"
include "oveq2.mm"
include "breq2d.mm"
include "ceqsexgv.mm"
include "bitr3d.mm"
include "anbi12d.mm"
include "anass.mm"
include "syl6bb.mm"
include "rexbidv2.mm"
include "ad2antrr.mm"
include "sylibrd.mm"
include "imdistanda.mm"
include "clat.mm"
include "hllat.mm"
include "simp2.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "pmapeq0.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "simp3.mm"
include "atn0.mm"
include "mpbird.mm"
include "elpaddn0.mm"
include "syl12anc.mm"
include "3imtr4d.mm"
include "ssrdv.mm"
include "pmapjoin.mm"
include "eqssd.mm"
include "pm2.61dane.mm"

theorem pmapjat1
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let cM: class M
  let cX: class X
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  assume pmapjat.b: |- B = ( Base ` K )
  assume pmapjat.j: |- .\/ = ( join ` K )
  assume pmapjat.a: |- A = ( Atoms ` K )
  assume pmapjat.m: |- M = ( pmap ` K )
  assume pmapjat.p: |- .+ = ( +P ` K )


  assert |- ( ( K e. HL /\ X e. B /\ Q e. A ) -> ( M ` ( X .\/ Q ) ) = ( ( M ` X ) .+ ( M ` Q ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cQ
    cA
    wcel
    #
    w3a
    #
    cX
    cQ
    c.or
    co
    #
    cM
    cfv
    #
    cX
    cM
    cfv
    #
    cQ
    cM
    cfv
    #
    c.pl
    co
    #
    wceq
    cX
    cK
    cp0
    cfv
    #
    @3
    cX
    @9
    wceq
    #
    wa
    #
    c0
    @7
    c.pl
    co
    #
    @7
    @8
    @5
    @3
    @12
    @7
    wceq
    #
    @10
    @3
    @0
    @7
    cA
    wss
    #
    @13
    @0
    @1
    @2
    simp1
    #
    @3
    @0
    cQ
    cB
    wcel
    #
    @14
    @15
    @2
    @0
    @16
    @1
    cA
    cB
    cQ
    cK
    pmapjat.b
    pmapjat.a
    atbase
    3ad2ant3
    #
    cA
    cB
    chlt
    cK
    cM
    cQ
    pmapjat.b
    pmapjat.a
    pmapjat.m
    pmapssat
    syl2anc
    #
    cA
    chlt
    c.pl
    cK
    @7
    pmapjat.a
    pmapjat.p
    padd02
    syl2anc
    adantr
    @11
    @6
    c0
    @7
    c.pl
    @10
    @3
    @6
    @9
    cM
    cfv
    #
    c0
    cX
    @9
    cM
    fveq2
    @3
    cK
    cal
    wcel
    #
    @19
    c0
    wceq
    @0
    @1
    @20
    @2
    cK
    hlatl
    3ad2ant1
    #
    cK
    cM
    @9
    @9
    eqid
    #
    pmapjat.m
    pmap0
    syl
    sylan9eqr
    oveq1d
    @11
    @4
    cQ
    cM
    @10
    @3
    @4
    @9
    cQ
    c.or
    co
    #
    cQ
    cX
    @9
    cQ
    c.or
    oveq1
    @3
    cK
    col
    wcel
    #
    @16
    @23
    cQ
    wceq
    @0
    @1
    @24
    @2
    cK
    hlol
    3ad2ant1
    @17
    cB
    c.or
    cK
    cQ
    @9
    pmapjat.b
    pmapjat.j
    @22
    olj02
    syl2anc
    sylan9eqr
    fveq2d
    3eqtr4rd
    @3
    cX
    @9
    wne
    #
    wa
    #
    @5
    @8
    @26
    vp
    @5
    @8
    @26
    vp
    cv
    #
    cA
    wcel
    #
    @27
    @4
    cK
    cple
    cfv
    #
    wbr
    #
    wa
    #
    @28
    @27
    vq
    cv
    #
    vr
    cv
    #
    c.or
    co
    #
    @29
    wbr
    #
    vr
    @7
    wrex
    #
    vq
    @6
    wrex
    #
    wa
    #
    @27
    @5
    wcel
    #
    @27
    @8
    wcel
    #
    @26
    @28
    @30
    @37
    @26
    @28
    wa
    #
    @30
    @32
    cX
    @29
    wbr
    #
    @27
    @32
    cQ
    c.or
    co
    #
    @29
    wbr
    #
    wa
    #
    vq
    cA
    wrex
    #
    @37
    @41
    @30
    @46
    @41
    @30
    wa
    #
    @0
    @1
    @28
    @2
    w3a
    #
    @25
    @30
    @46
    @41
    @0
    @30
    @0
    @1
    @2
    @25
    @28
    simpll1
    adantr
    @47
    @1
    @28
    @2
    @41
    @1
    @30
    @0
    @1
    @2
    @25
    @28
    simpll2
    adantr
    @26
    @28
    @30
    simplr
    @41
    @2
    @30
    @0
    @1
    @2
    @25
    @28
    simpll3
    adantr
    3jca
    @3
    @25
    @28
    @30
    simpllr
    @41
    @30
    simpr
    @0
    @48
    wa
    @25
    @30
    wa
    @46
    cA
    cB
    @27
    cQ
    c.or
    cK
    @29
    cX
    @9
    vq
    pmapjat.b
    @29
    eqid
    #
    pmapjat.j
    @22
    pmapjat.a
    cvrat42
    imp
    syl22anc
    ex
    @3
    @37
    @46
    wb
    @25
    @28
    @3
    @36
    @45
    vq
    @6
    cA
    @3
    @32
    @6
    wcel
    #
    @36
    wa
    @32
    cA
    wcel
    #
    @42
    wa
    #
    @44
    wa
    @51
    @45
    wa
    @3
    @50
    @52
    @36
    @44
    @0
    @1
    @50
    @52
    wb
    @2
    cA
    cB
    chlt
    @32
    cK
    @29
    cM
    cX
    pmapjat.b
    @49
    pmapjat.a
    pmapjat.m
    elpmap
    3adant3
    @3
    @33
    cQ
    wceq
    #
    @35
    wa
    #
    vr
    wex
    #
    @36
    @44
    @36
    @33
    @7
    wcel
    #
    @35
    wa
    #
    vr
    wex
    @3
    @55
    @35
    vr
    @7
    df-rex
    @3
    @57
    @54
    vr
    @3
    @56
    @53
    @35
    @0
    @2
    @56
    @53
    wb
    @1
    cA
    cQ
    cK
    cM
    @33
    pmapjat.a
    pmapjat.m
    elpmapat
    3adant2
    anbi1d
    exbidv
    syl5rbb
    @2
    @0
    @55
    @44
    wb
    @1
    @35
    @44
    vr
    cQ
    cA
    @53
    @34
    @43
    @27
    @29
    @33
    cQ
    @32
    c.or
    oveq2
    breq2d
    ceqsexgv
    3ad2ant3
    bitr3d
    anbi12d
    @51
    @42
    @44
    anass
    syl6bb
    rexbidv2
    ad2antrr
    sylibrd
    imdistanda
    @3
    @39
    @31
    wb
    #
    @25
    @3
    @0
    @4
    cB
    wcel
    #
    @58
    @15
    @3
    cK
    clat
    wcel
    #
    @1
    @16
    @59
    @0
    @1
    @60
    @2
    cK
    hllat
    3ad2ant1
    #
    @0
    @1
    @2
    simp2
    #
    @17
    cB
    c.or
    cK
    cX
    cQ
    pmapjat.b
    pmapjat.j
    latjcl
    syl3anc
    cA
    cB
    chlt
    @27
    cK
    @29
    cM
    @4
    pmapjat.b
    @49
    pmapjat.a
    pmapjat.m
    elpmap
    syl2anc
    adantr
    @26
    @60
    @6
    cA
    wss
    #
    @14
    w3a
    #
    @6
    c0
    wne
    #
    @7
    c0
    wne
    #
    @40
    @38
    wb
    @3
    @64
    @25
    @3
    @60
    @63
    @14
    @61
    @0
    @1
    @63
    @2
    cA
    cB
    chlt
    cK
    cM
    cX
    pmapjat.b
    pmapjat.a
    pmapjat.m
    pmapssat
    3adant3
    @18
    3jca
    adantr
    @3
    @65
    @25
    @3
    @6
    c0
    cX
    @9
    @0
    @1
    @6
    c0
    wceq
    @10
    wb
    @2
    cB
    cK
    cM
    cX
    @9
    pmapjat.b
    @22
    pmapjat.m
    pmapeq0
    3adant3
    necon3bid
    biimpar
    @3
    @66
    @25
    @3
    @66
    cQ
    @9
    wne
    #
    @3
    @20
    @2
    @67
    @21
    @0
    @1
    @2
    simp3
    cA
    cQ
    cK
    @9
    @22
    pmapjat.a
    atn0
    syl2anc
    @3
    @7
    c0
    cQ
    @9
    @3
    @0
    @16
    @7
    c0
    wceq
    cQ
    @9
    wceq
    wb
    @15
    @17
    cB
    cK
    cM
    cQ
    @9
    pmapjat.b
    @22
    pmapjat.m
    pmapeq0
    syl2anc
    necon3bid
    mpbird
    adantr
    cA
    c.pl
    @27
    c.or
    cK
    @29
    @6
    @7
    vr
    vq
    @49
    pmapjat.j
    pmapjat.a
    pmapjat.p
    elpaddn0
    syl12anc
    3imtr4d
    ssrdv
    @3
    @8
    @5
    wss
    #
    @25
    @3
    @60
    @1
    @16
    @68
    @61
    @62
    @17
    cB
    c.pl
    c.or
    cK
    cM
    cX
    cQ
    pmapjat.b
    pmapjat.j
    pmapjat.m
    pmapjat.p
    pmapjoin
    syl3anc
    adantr
    eqssd
    pm2.61dane
end
