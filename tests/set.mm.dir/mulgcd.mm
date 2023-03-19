include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "cmul.mm"
include "co.mm"
include "cgcd.mm"
include "wceq.mm"
include "cn.mm"
include "cc0.mm"
include "wo.mm"
include "wa.mm"
include "wi.mm"
include "elnn0.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "simp1.mm"
include "nnzd.mm"
include "simp2.mm"
include "zmulcld.mm"
include "simp3.mm"
include "gcdcld.mm"
include "nnnn0d.mm"
include "gcdcl.mm"
include "3adant1.mm"
include "nn0mulcld.mm"
include "cdiv.mm"
include "nn0cnd.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcan2d.mm"
include "gcddvds.mm"
include "syl2anc.mm"
include "simpld.mm"
include "eqbrtrd.mm"
include "wne.mm"
include "wb.mm"
include "dvdsmul1.mm"
include "dvdsgcd.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "nn0zd.mm"
include "dvdsval2.mm"
include "mpbid.mm"
include "dvdscmulr.mm"
include "syl112anc.mm"
include "simprd.mm"
include "dvdscmul.mm"
include "mpd.mm"
include "eqbrtrrd.mm"
include "dvdseq.mm"
include "syl22anc.mm"
include "3expib.mm"
include "mul02d.mm"
include "gcd0val.mm"
include "syl6reqr.mm"
include "oveq1d.mm"
include "cc.mm"
include "zcn.mm"
include "3ad2ant2.mm"
include "eqtrd.mm"
include "3ad2ant3.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "jaoi.mm"
include "sylbi.mm"
include "3impib.mm"

theorem mulgcd
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( K e. NN0 /\ M e. ZZ /\ N e. ZZ ) -> ( ( K x. M ) gcd ( K x. N ) ) = ( K x. ( M gcd N ) ) )

  proof
    cK
    cn0
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cK
    cM
    cmul
    co
    #
    cK
    cN
    cmul
    co
    #
    cgcd
    co
    #
    cK
    cM
    cN
    cgcd
    co
    #
    cmul
    co
    #
    wceq
    #
    @0
    cK
    cn
    wcel
    #
    cK
    cc0
    wceq
    #
    wo
    @1
    @2
    wa
    @8
    wi
    #
    cK
    elnn0
    @9
    @11
    @10
    @9
    @1
    @2
    @8
    @9
    @1
    @2
    w3a
    #
    @5
    cn0
    wcel
    @7
    cn0
    wcel
    @5
    @7
    cdvds
    wbr
    @7
    @5
    cdvds
    wbr
    #
    @8
    @12
    @3
    @4
    @12
    cK
    cM
    @12
    cK
    @9
    @1
    @2
    simp1
    #
    nnzd
    #
    @9
    @1
    @2
    simp2
    #
    zmulcld
    #
    @12
    cK
    cN
    @15
    @9
    @1
    @2
    simp3
    #
    zmulcld
    #
    gcdcld
    #
    @12
    cK
    @6
    @12
    cK
    @14
    nnnn0d
    @1
    @2
    @6
    cn0
    wcel
    #
    @9
    cM
    cN
    gcdcl
    #
    3adant1
    #
    nn0mulcld
    #
    @12
    cK
    @5
    cK
    cdiv
    co
    #
    cmul
    co
    #
    @5
    @7
    cdvds
    @12
    @5
    cK
    @12
    @5
    @20
    nn0cnd
    @12
    cK
    @14
    nncnd
    @12
    cK
    @14
    nnne0d
    #
    divcan2d
    #
    @12
    @25
    @6
    cdvds
    wbr
    #
    @26
    @7
    cdvds
    wbr
    #
    @12
    @25
    cM
    cdvds
    wbr
    #
    @25
    cN
    cdvds
    wbr
    #
    @29
    @12
    @26
    @3
    cdvds
    wbr
    #
    @31
    @12
    @26
    @5
    @3
    cdvds
    @28
    @12
    @5
    @3
    cdvds
    wbr
    #
    @5
    @4
    cdvds
    wbr
    #
    @12
    @3
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @34
    @35
    wa
    @17
    @19
    @3
    @4
    gcddvds
    syl2anc
    #
    simpld
    eqbrtrd
    @12
    @25
    cz
    wcel
    #
    @1
    cK
    cz
    wcel
    #
    cK
    cc0
    wne
    #
    @33
    @31
    wb
    @12
    cK
    @5
    cdvds
    wbr
    #
    @39
    @12
    cK
    @3
    cdvds
    wbr
    #
    cK
    @4
    cdvds
    wbr
    #
    @42
    @12
    @40
    @1
    @43
    @15
    @16
    cK
    cM
    dvdsmul1
    syl2anc
    @12
    @40
    @2
    @44
    @15
    @18
    cK
    cN
    dvdsmul1
    syl2anc
    @12
    @40
    @36
    @37
    @43
    @44
    wa
    @42
    wi
    @15
    @17
    @19
    cK
    @3
    @4
    dvdsgcd
    syl3anc
    mp2and
    @12
    @40
    @41
    @5
    cz
    wcel
    @42
    @39
    wb
    @15
    @27
    @12
    @5
    @20
    nn0zd
    cK
    @5
    dvdsval2
    syl3anc
    mpbid
    #
    @16
    @15
    @27
    cK
    @25
    cM
    dvdscmulr
    syl112anc
    mpbid
    @12
    @26
    @4
    cdvds
    wbr
    #
    @32
    @12
    @26
    @5
    @4
    cdvds
    @28
    @12
    @34
    @35
    @38
    simprd
    eqbrtrd
    @12
    @39
    @2
    @40
    @41
    @46
    @32
    wb
    @45
    @18
    @15
    @27
    cK
    @25
    cN
    dvdscmulr
    syl112anc
    mpbid
    @12
    @39
    @1
    @2
    @31
    @32
    wa
    @29
    wi
    @45
    @16
    @18
    @25
    cM
    cN
    dvdsgcd
    syl3anc
    mp2and
    @12
    @39
    @6
    cz
    wcel
    #
    @40
    @29
    @30
    wi
    @45
    @12
    @6
    @23
    nn0zd
    #
    @15
    cK
    @25
    @6
    dvdscmul
    syl3anc
    mpd
    eqbrtrrd
    @12
    @7
    @3
    cdvds
    wbr
    #
    @7
    @4
    cdvds
    wbr
    #
    @13
    @12
    @6
    cM
    cdvds
    wbr
    #
    @49
    @12
    @51
    @6
    cN
    cdvds
    wbr
    #
    @1
    @2
    @51
    @52
    wa
    @9
    cM
    cN
    gcddvds
    3adant1
    #
    simpld
    @12
    @47
    @1
    @40
    @51
    @49
    wi
    @48
    @16
    @15
    cK
    @6
    cM
    dvdscmul
    syl3anc
    mpd
    @12
    @52
    @50
    @12
    @51
    @52
    @53
    simprd
    @12
    @47
    @2
    @40
    @52
    @50
    wi
    @48
    @18
    @15
    cK
    @6
    cN
    dvdscmul
    syl3anc
    mpd
    @12
    @7
    cz
    wcel
    @36
    @37
    @49
    @50
    wa
    @13
    wi
    @12
    @7
    @24
    nn0zd
    @17
    @19
    @7
    @3
    @4
    dvdsgcd
    syl3anc
    mp2and
    @5
    @7
    dvdseq
    syl22anc
    3expib
    @10
    @1
    @2
    @8
    @10
    @1
    @2
    w3a
    #
    cc0
    cc0
    cgcd
    co
    #
    cc0
    @6
    cmul
    co
    #
    @5
    @7
    @54
    @56
    cc0
    @55
    @54
    @6
    @54
    @6
    @1
    @2
    @21
    @10
    @22
    3adant1
    nn0cnd
    mul02d
    gcd0val
    syl6reqr
    @54
    @3
    cc0
    @4
    cc0
    cgcd
    @54
    @3
    cc0
    cM
    cmul
    co
    cc0
    @54
    cK
    cc0
    cM
    cmul
    @10
    @1
    @2
    simp1
    #
    oveq1d
    @54
    cM
    @1
    @10
    cM
    cc
    wcel
    @2
    cM
    zcn
    3ad2ant2
    mul02d
    eqtrd
    @54
    @4
    cc0
    cN
    cmul
    co
    cc0
    @54
    cK
    cc0
    cN
    cmul
    @57
    oveq1d
    @54
    cN
    @2
    @10
    cN
    cc
    wcel
    @1
    cN
    zcn
    3ad2ant3
    mul02d
    eqtrd
    oveq12d
    @54
    cK
    cc0
    @6
    cmul
    @57
    oveq1d
    3eqtr4d
    3expib
    jaoi
    sylbi
    3impib
end
