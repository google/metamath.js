include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "cfz.mm"
include "caddc.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "clt.mm"
include "wbr.mm"
include "simpr.mm"
include "cr.mm"
include "zre.mm"
include "ad2antlr.mm"
include "ltm1d.mm"
include "eqbrtrd.mm"
include "wb.mm"
include "simplr.mm"
include "eluzelz.mm"
include "ad2antrr.mm"
include "fzn.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "difid.mm"
include "a1i.mm"
include "eqcomd.mm"
include "oveq1.mm"
include "adantl.mm"
include "cc.mm"
include "recnd.mm"
include "1cnd.mm"
include "npcand.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "fzsn.mm"
include "eqtr2d.mm"
include "sneqd.mm"
include "difeq12d.mm"
include "3eqtrd.mm"
include "wn.mm"
include "cle.mm"
include "w3a.mm"
include "1red.mm"
include "resubcld.mm"
include "zred.mm"
include "eluzle.mm"
include "wne.mm"
include "neqne.mm"
include "leneltd.mm"
include "zlem1lt.mm"
include "mpbird.mm"
include "3jca.mm"
include "eluz2.mm"
include "sylibr.mm"
include "fzdifsuc.mm"
include "syl.mm"
include "pm2.61dan.mm"
include "eluzel2.mm"
include "con3i.mm"
include "fzn0.mm"
include "sylnibr.mm"
include "nne.mm"
include "sylib.mm"
include "difeq1d.mm"
include "0dif.mm"

theorem fzdifsuc2
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` ( M - 1 ) ) -> ( M ... N ) = ( ( M ... ( N + 1 ) ) \ { ( N + 1 ) } ) )

  proof
    cN
    cM
    c1
    cmin
    co
    #
    cuz
    cfv
    wcel
    #
    cM
    cz
    wcel
    #
    cM
    cN
    cfz
    co
    #
    cM
    cN
    c1
    caddc
    co
    #
    cfz
    co
    #
    @4
    csn
    #
    cdif
    #
    wceq
    #
    @1
    @2
    wa
    #
    cN
    @0
    wceq
    #
    @8
    @9
    @10
    wa
    #
    @3
    c0
    cM
    csn
    #
    @12
    cdif
    #
    @7
    @11
    cN
    cM
    clt
    wbr
    #
    @3
    c0
    wceq
    #
    @11
    cN
    @0
    cM
    clt
    @9
    @10
    simpr
    @11
    cM
    @2
    cM
    cr
    wcel
    #
    @1
    @10
    cM
    zre
    #
    ad2antlr
    ltm1d
    eqbrtrd
    @11
    @2
    cN
    cz
    wcel
    #
    @14
    @15
    wb
    @1
    @2
    @10
    simplr
    @1
    @18
    @2
    @10
    @0
    cN
    eluzelz
    #
    ad2antrr
    cM
    cN
    fzn
    syl2anc
    mpbid
    @11
    @13
    c0
    @13
    c0
    wceq
    @11
    @12
    difid
    a1i
    eqcomd
    @11
    @12
    @5
    @12
    @6
    @11
    @5
    cM
    cM
    cfz
    co
    #
    @12
    @11
    @4
    cM
    cM
    cfz
    @11
    @4
    @0
    c1
    caddc
    co
    #
    cM
    @10
    @4
    @21
    wceq
    @9
    cN
    @0
    c1
    caddc
    oveq1
    adantl
    @11
    cM
    c1
    @2
    cM
    cc
    wcel
    @1
    @10
    @2
    cM
    @17
    recnd
    ad2antlr
    @11
    1cnd
    npcand
    eqtrd
    #
    oveq2d
    @2
    @20
    @12
    wceq
    @1
    @10
    cM
    fzsn
    ad2antlr
    eqtr2d
    @11
    cM
    @4
    @11
    @4
    cM
    @22
    eqcomd
    sneqd
    difeq12d
    3eqtrd
    @9
    @10
    wn
    #
    wa
    #
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    @8
    @24
    @2
    @18
    cM
    cN
    cle
    wbr
    #
    w3a
    @26
    @24
    @2
    @18
    @27
    @1
    @2
    @23
    simplr
    #
    @1
    @18
    @2
    @23
    @19
    ad2antrr
    #
    @24
    @27
    @0
    cN
    clt
    wbr
    #
    @24
    @0
    cN
    @24
    cM
    c1
    @2
    @16
    @1
    @23
    @17
    ad2antlr
    @24
    1red
    resubcld
    @24
    cN
    @29
    zred
    @1
    @0
    cN
    cle
    wbr
    @2
    @23
    @0
    cN
    eluzle
    ad2antrr
    @23
    cN
    @0
    wne
    @9
    cN
    @0
    neqne
    adantl
    leneltd
    @24
    @2
    @18
    @27
    @30
    wb
    @28
    @29
    cM
    cN
    zlem1lt
    syl2anc
    mpbird
    3jca
    cM
    cN
    eluz2
    sylibr
    cM
    cN
    fzdifsuc
    syl
    pm2.61dan
    @2
    wn
    #
    @8
    @1
    @31
    @3
    c0
    @7
    @31
    @3
    c0
    wne
    #
    wn
    @15
    @31
    @26
    @32
    @26
    @2
    cM
    cN
    eluzel2
    con3i
    cM
    cN
    fzn0
    sylnibr
    @3
    c0
    nne
    sylib
    @31
    @7
    c0
    @6
    cdif
    #
    c0
    @31
    @5
    c0
    @6
    @31
    @5
    c0
    wne
    #
    wn
    @5
    c0
    wceq
    @31
    @4
    @25
    wcel
    #
    @34
    @35
    @2
    cM
    @4
    eluzel2
    con3i
    cM
    @4
    fzn0
    sylnibr
    @5
    c0
    nne
    sylib
    difeq1d
    @33
    c0
    wceq
    @31
    @6
    0dif
    a1i
    eqtr2d
    eqtrd
    adantl
    pm2.61dan
end
