include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "wceq.mm"
include "crelexp.mm"
include "co.mm"
include "wo.mm"
include "wi.mm"
include "elpri.mm"
include "w3a.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "dmresi.mm"
include "rnresi.mm"
include "uneq12i.mm"
include "unidm.mm"
include "eqtri.mm"
include "reseq2i.mm"
include "simp1.mm"
include "oveq2d.mm"
include "simp3l.mm"
include "relexp0g.mm"
include "syl.mm"
include "eqtrd.mm"
include "simp2.mm"
include "oveq12d.mm"
include "cvv.mm"
include "dmexg.mm"
include "rnexg.mm"
include "unexg.mm"
include "syl2anc.mm"
include "resiexd.mm"
include "3syl.mm"
include "simp3r.mm"
include "0re.mm"
include "ltnri.mm"
include "breq12d.mm"
include "mtbiri.mm"
include "iffalsed.mm"
include "3eqtrd.mm"
include "3eqtr4a.mm"
include "3exp.mm"
include "relexp1g.mm"
include "wn.mm"
include "0lt1.mm"
include "1re.mm"
include "ltnsymi.mm"
include "mp1i.mm"
include "mtbird.mm"
include "eqtr4d.mm"
include "jaoi.mm"
include "ovex.mm"
include "mpbiri.mm"
include "iftrued.mm"
include "3eqtr4d.mm"
include "jaod.mm"
include "imp.mm"
include "syl2an.mm"
include "impcom.mm"

theorem relexp01min
  let cR: class R
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V


  assert |- ( ( ( R e. V /\ I = if ( J < K , J , K ) ) /\ ( J e. { 0 , 1 } /\ K e. { 0 , 1 } ) ) -> ( ( R ^r J ) ^r K ) = ( R ^r I ) )

  proof
    cJ
    cc0
    c1
    cpr
    #
    wcel
    #
    cK
    @0
    wcel
    #
    wa
    cR
    cV
    wcel
    #
    cI
    cJ
    cK
    clt
    wbr
    #
    cJ
    cK
    cif
    #
    wceq
    #
    wa
    #
    cR
    cJ
    crelexp
    co
    #
    cK
    crelexp
    co
    #
    cR
    cI
    crelexp
    co
    #
    wceq
    #
    @1
    cJ
    cc0
    wceq
    #
    cJ
    c1
    wceq
    #
    wo
    #
    cK
    cc0
    wceq
    #
    cK
    c1
    wceq
    #
    wo
    #
    @7
    @11
    wi
    #
    @2
    cJ
    cc0
    c1
    elpri
    cK
    cc0
    c1
    elpri
    @14
    @17
    @18
    @14
    @15
    @18
    @16
    @12
    @15
    @18
    wi
    @13
    @12
    @15
    @7
    @11
    @12
    @15
    @7
    w3a
    #
    cid
    cid
    cR
    cdm
    #
    cR
    crn
    #
    cun
    #
    cres
    #
    cdm
    #
    @23
    crn
    #
    cun
    #
    cres
    #
    @23
    @9
    @10
    @26
    @22
    cid
    @26
    @22
    @22
    cun
    @22
    @24
    @22
    @25
    @22
    @22
    dmresi
    @22
    rnresi
    uneq12i
    @22
    unidm
    eqtri
    reseq2i
    @19
    @9
    @23
    cc0
    crelexp
    co
    #
    @27
    @19
    @8
    @23
    cK
    cc0
    crelexp
    @19
    @8
    cR
    cc0
    crelexp
    co
    #
    @23
    @19
    cJ
    cc0
    cR
    crelexp
    @12
    @15
    @7
    simp1
    #
    oveq2d
    @19
    @3
    @29
    @23
    wceq
    @12
    @15
    @3
    @6
    simp3l
    #
    cR
    cV
    relexp0g
    syl
    #
    eqtrd
    @12
    @15
    @7
    simp2
    #
    oveq12d
    @19
    @3
    @23
    cvv
    wcel
    @28
    @27
    wceq
    @31
    @3
    @22
    cvv
    @3
    @20
    cvv
    wcel
    @21
    cvv
    wcel
    @22
    cvv
    wcel
    cR
    cV
    dmexg
    cR
    cV
    rnexg
    @20
    @21
    cvv
    cvv
    unexg
    syl2anc
    resiexd
    @23
    cvv
    relexp0g
    3syl
    eqtrd
    @19
    @10
    @29
    @23
    @19
    cI
    cc0
    cR
    crelexp
    @19
    cI
    @5
    cK
    cc0
    @12
    @15
    @3
    @6
    simp3r
    @19
    @4
    cJ
    cK
    @19
    @4
    cc0
    cc0
    clt
    wbr
    cc0
    0re
    ltnri
    @19
    cJ
    cc0
    cK
    cc0
    clt
    @30
    @33
    breq12d
    mtbiri
    iffalsed
    @33
    3eqtrd
    oveq2d
    @32
    eqtrd
    3eqtr4a
    3exp
    @13
    @15
    @7
    @11
    @13
    @15
    @7
    w3a
    #
    @9
    @29
    @10
    @34
    @8
    cR
    cK
    cc0
    crelexp
    @34
    @8
    cR
    c1
    crelexp
    co
    #
    cR
    @34
    cJ
    c1
    cR
    crelexp
    @13
    @15
    @7
    simp1
    #
    oveq2d
    @34
    @3
    @35
    cR
    wceq
    #
    @13
    @15
    @3
    @6
    simp3l
    cR
    cV
    relexp1g
    #
    syl
    eqtrd
    @13
    @15
    @7
    simp2
    #
    oveq12d
    @34
    cI
    cc0
    cR
    crelexp
    @34
    cI
    @5
    cK
    cc0
    @13
    @15
    @3
    @6
    simp3r
    @34
    @4
    cJ
    cK
    @34
    @4
    c1
    cc0
    clt
    wbr
    #
    cc0
    c1
    clt
    wbr
    #
    @40
    wn
    @34
    0lt1
    cc0
    c1
    0re
    1re
    ltnsymi
    mp1i
    @34
    cJ
    c1
    cK
    cc0
    clt
    @36
    @39
    breq12d
    mtbird
    iffalsed
    @39
    3eqtrd
    oveq2d
    eqtr4d
    3exp
    jaoi
    @12
    @16
    @18
    wi
    @13
    @12
    @16
    @7
    @11
    @12
    @16
    @7
    w3a
    #
    @29
    c1
    crelexp
    co
    #
    @29
    @9
    @10
    @29
    cvv
    wcel
    @43
    @29
    wceq
    @42
    cR
    cc0
    crelexp
    ovex
    @29
    cvv
    relexp1g
    mp1i
    @42
    @8
    @29
    cK
    c1
    crelexp
    @42
    cJ
    cc0
    cR
    crelexp
    @12
    @16
    @7
    simp1
    #
    oveq2d
    @12
    @16
    @7
    simp2
    #
    oveq12d
    @42
    cI
    cc0
    cR
    crelexp
    @42
    cI
    @5
    cJ
    cc0
    @12
    @16
    @3
    @6
    simp3r
    @42
    @4
    cJ
    cK
    @42
    @4
    @41
    0lt1
    @42
    cJ
    cc0
    cK
    c1
    clt
    @44
    @45
    breq12d
    mpbiri
    iftrued
    @44
    3eqtrd
    oveq2d
    3eqtr4d
    3exp
    @13
    @16
    @7
    @11
    @13
    @16
    @7
    w3a
    #
    @9
    @35
    @10
    @46
    @8
    cR
    cK
    c1
    crelexp
    @46
    @8
    @35
    cR
    @46
    cJ
    c1
    cR
    crelexp
    @13
    @16
    @7
    simp1
    #
    oveq2d
    @46
    @3
    @37
    @13
    @16
    @3
    @6
    simp3l
    @38
    syl
    eqtrd
    @13
    @16
    @7
    simp2
    #
    oveq12d
    @46
    cI
    c1
    cR
    crelexp
    @46
    cI
    @5
    cK
    c1
    @13
    @16
    @3
    @6
    simp3r
    @46
    @4
    cJ
    cK
    @46
    @4
    c1
    c1
    clt
    wbr
    c1
    1re
    ltnri
    @46
    cJ
    c1
    cK
    c1
    clt
    @47
    @48
    breq12d
    mtbiri
    iffalsed
    @48
    3eqtrd
    oveq2d
    eqtr4d
    3exp
    jaoi
    jaod
    imp
    syl2an
    impcom
end
