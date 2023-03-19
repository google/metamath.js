include "wss.mm"
include "cxp.mm"
include "cdif.mm"
include "cima.mm"
include "wceq.mm"
include "c0.mm"
include "ima0.mm"
include "imaeq2.mm"
include "syl6eq.mm"
include "difeq1d.mm"
include "0dif.mm"
include "3eqtr4a.mm"
include "adantl.mm"
include "wne.mm"
include "wa.mm"
include "cun.mm"
include "cin.mm"
include "inundif.mm"
include "imaeq1i.mm"
include "imaundir.mm"
include "eqtr3i.mm"
include "difeq1i.mm"
include "difundir.mm"
include "eqtri.mm"
include "inss2.mm"
include "imass1.mm"
include "ssdif.mm"
include "mp2b.mm"
include "cif.mm"
include "xpima.mm"
include "wn.mm"
include "incom.mm"
include "df-ss.mm"
include "biimpi.mm"
include "syl5eqr.mm"
include "simpl.mm"
include "eqnetrd.mm"
include "df-ne.mm"
include "iffalse.mm"
include "3syl.mm"
include "syl5eq.mm"
include "difid.mm"
include "syl5sseq.mm"
include "ss0.mm"
include "syl.mm"
include "cvv.mm"
include "crn.mm"
include "cres.mm"
include "df-ima.mm"
include "df-res.mm"
include "rneqi.mm"
include "ineq1i.mm"
include "xpss1.mm"
include "sslin.mm"
include "rnss.mm"
include "ssn0.mm"
include "ancoms.mm"
include "inss1.mm"
include "ax-mp.mm"
include "indif2.mm"
include "difxp2.mm"
include "3sstr4i.mm"
include "mp1i.mm"
include "rnxp.mm"
include "sseqtrd.mm"
include "disj2.mm"
include "sylibr.mm"
include "ssdisj.mm"
include "syl2anc.mm"
include "disj3.mm"
include "sylib.mm"
include "eqcomd.mm"
include "uneq12d.mm"
include "uncom.mm"
include "un0.mm"
include "eqtr2i.mm"
include "syl6reqr.mm"
include "pm2.61dane.mm"

theorem imadifxp
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R


  assert |- ( C C_ A -> ( ( R \ ( A X. B ) ) " C ) = ( ( R " C ) \ B ) )

  proof
    cC
    cA
    wss
    #
    cR
    cA
    cB
    cxp
    #
    cdif
    #
    cC
    cima
    #
    cR
    cC
    cima
    #
    cB
    cdif
    #
    wceq
    #
    cC
    c0
    cC
    c0
    wceq
    #
    @6
    @0
    @7
    @2
    c0
    cima
    c0
    @3
    @5
    @2
    ima0
    cC
    c0
    @2
    imaeq2
    @7
    @5
    c0
    cB
    cdif
    c0
    @7
    @4
    c0
    cB
    @7
    @4
    cR
    c0
    cima
    c0
    cC
    c0
    cR
    imaeq2
    cR
    ima0
    syl6eq
    difeq1d
    cB
    0dif
    syl6eq
    3eqtr4a
    adantl
    cC
    c0
    wne
    #
    @0
    @6
    @8
    @0
    wa
    #
    @5
    c0
    @3
    cun
    #
    @3
    @9
    @5
    cR
    @1
    cin
    #
    cC
    cima
    #
    cB
    cdif
    #
    @3
    cB
    cdif
    #
    cun
    #
    @10
    @5
    @12
    @3
    cun
    #
    cB
    cdif
    @15
    @4
    @16
    cB
    @11
    @2
    cun
    #
    cC
    cima
    @4
    @16
    @17
    cR
    cC
    cR
    @1
    inundif
    imaeq1i
    @11
    @2
    cC
    imaundir
    eqtr3i
    difeq1i
    @12
    @3
    cB
    difundir
    eqtri
    @9
    @13
    c0
    @14
    @3
    @9
    @13
    c0
    wss
    @13
    c0
    wceq
    @9
    @1
    cC
    cima
    #
    cB
    cdif
    #
    @13
    c0
    @11
    @1
    wss
    @12
    @18
    wss
    @13
    @19
    wss
    cR
    @1
    inss2
    @11
    @1
    cC
    imass1
    @12
    @18
    cB
    ssdif
    mp2b
    @9
    @19
    cB
    cB
    cdif
    c0
    @9
    @18
    cB
    cB
    @9
    @18
    cA
    cC
    cin
    #
    c0
    wceq
    #
    c0
    cB
    cif
    #
    cB
    cA
    cB
    cC
    xpima
    @9
    @20
    c0
    wne
    #
    @21
    wn
    #
    @22
    cB
    wceq
    @9
    @20
    cC
    c0
    @0
    @20
    cC
    wceq
    @8
    @0
    @20
    cC
    cA
    cin
    #
    cC
    cC
    cA
    incom
    @0
    @25
    cC
    wceq
    cC
    cA
    df-ss
    biimpi
    syl5eqr
    adantl
    @8
    @0
    simpl
    eqnetrd
    @23
    @24
    @20
    c0
    df-ne
    biimpi
    @21
    c0
    cB
    iffalse
    3syl
    syl5eq
    difeq1d
    cB
    difid
    syl6eq
    syl5sseq
    @13
    ss0
    syl
    @9
    @3
    @14
    @9
    @3
    cB
    cin
    #
    c0
    wceq
    @3
    @14
    wceq
    @9
    @26
    @2
    cC
    cvv
    cxp
    #
    cin
    #
    crn
    #
    cB
    cin
    #
    c0
    @3
    @29
    cB
    @3
    @2
    cC
    cres
    #
    crn
    @29
    @2
    cC
    df-ima
    @31
    @28
    @2
    cC
    df-res
    rneqi
    eqtri
    ineq1i
    @9
    @29
    @2
    cA
    cvv
    cxp
    #
    cin
    #
    crn
    #
    wss
    #
    @34
    cB
    cin
    c0
    wceq
    #
    @30
    c0
    wceq
    @0
    @35
    @8
    @0
    @27
    @32
    wss
    @28
    @33
    wss
    @35
    cC
    cA
    cvv
    xpss1
    @27
    @32
    @2
    sslin
    @28
    @33
    rnss
    3syl
    adantl
    @9
    cA
    c0
    wne
    #
    @36
    @0
    @8
    @37
    cC
    cA
    ssn0
    ancoms
    @37
    @34
    cvv
    cB
    cdif
    #
    wss
    @36
    @37
    @34
    cA
    @38
    cxp
    #
    crn
    #
    @38
    @33
    @39
    wss
    @34
    @40
    wss
    @37
    @32
    cR
    cin
    #
    @1
    cdif
    #
    @32
    @1
    cdif
    #
    @33
    @39
    @41
    @32
    wss
    @42
    @43
    wss
    @32
    cR
    inss1
    @41
    @32
    @1
    ssdif
    ax-mp
    @32
    @2
    cin
    @33
    @42
    @32
    @2
    incom
    @32
    cR
    @1
    indif2
    eqtr3i
    cA
    cvv
    cB
    difxp2
    3sstr4i
    @33
    @39
    rnss
    mp1i
    cA
    @38
    rnxp
    sseqtrd
    @34
    cB
    disj2
    sylibr
    syl
    @29
    @34
    cB
    ssdisj
    syl2anc
    syl5eq
    @3
    cB
    disj3
    sylib
    eqcomd
    uneq12d
    syl5eq
    @10
    @3
    c0
    cun
    @3
    c0
    @3
    uncom
    @3
    un0
    eqtr2i
    syl6reqr
    ancoms
    pm2.61dane
end
