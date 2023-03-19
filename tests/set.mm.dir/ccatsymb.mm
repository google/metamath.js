include "cword.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cif.mm"
include "cconcat.mm"
include "cc0.mm"
include "cle.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "cfzo.mm"
include "id.mm"
include "3adant3.mm"
include "ad2antrl.mm"
include "simpr.mm"
include "anim2i.mm"
include "wb.mm"
include "simp3.mm"
include "0zd.mm"
include "lencl.mm"
include "nn0zd.mm"
include "3ad2ant1.mm"
include "3jca.mm"
include "elfzo.mm"
include "syl.mm"
include "mpbird.mm"
include "df-3an.mm"
include "sylanbrc.mm"
include "ccatval1.mm"
include "eqcomd.mm"
include "ex.mm"
include "wn.mm"
include "cr.mm"
include "zre.mm"
include "0red.mm"
include "jca.mm"
include "3ad2ant3.mm"
include "ltnle.mm"
include "c0.mm"
include "wo.mm"
include "3adant2.mm"
include "adantr.mm"
include "orcd.mm"
include "wrdsymb0.mm"
include "sylc.mm"
include "ccatcl.mm"
include "eqtr4d.mm"
include "sylbird.mm"
include "com12.mm"
include "pm2.61i.mm"
include "caddc.mm"
include "nn0red.mm"
include "lenlt.mm"
include "syl2an.mm"
include "biimpar.mm"
include "ancomd.mm"
include "zaddcl.mm"
include "ccatval2.mm"
include "readdcl.mm"
include "lenltd.mm"
include "ccatlen.mm"
include "eqbrtrd.mm"
include "olcd.mm"
include "simp2.mm"
include "zsubcl.mm"
include "sylan2.mm"
include "ancoms.mm"
include "leaddsub2.mm"
include "syl3an.mm"
include "biimpa.mm"
include "ifeqda.mm"

theorem ccatsymb
  let cA: class A
  let cB: class B
  let cI: class I
  let cV: class V


  assert |- ( ( A e. Word V /\ B e. Word V /\ I e. ZZ ) -> ( ( A ++ B ) ` I ) = if ( I < ( # ` A ) , ( A ` I ) , ( B ` ( I - ( # ` A ) ) ) ) )

  proof
    cA
    cV
    cword
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cI
    cz
    wcel
    #
    w3a
    #
    cI
    cA
    chash
    cfv
    #
    clt
    wbr
    #
    cI
    cA
    cfv
    #
    cI
    @5
    cmin
    co
    #
    cB
    cfv
    #
    cif
    cI
    cA
    cB
    cconcat
    co
    #
    cfv
    #
    @4
    @6
    @7
    @9
    @11
    cc0
    cI
    cle
    wbr
    #
    @4
    @6
    wa
    #
    @7
    @11
    wceq
    #
    wi
    @12
    @13
    @14
    @12
    @13
    wa
    #
    @1
    @2
    cI
    cc0
    @5
    cfzo
    co
    wcel
    #
    w3a
    #
    @14
    @15
    @1
    @2
    wa
    #
    @16
    @17
    @4
    @18
    @12
    @6
    @1
    @2
    @18
    @3
    @18
    id
    3adant3
    #
    ad2antrl
    @15
    @16
    @12
    @6
    wa
    #
    @13
    @6
    @12
    @4
    @6
    simpr
    anim2i
    @15
    @3
    cc0
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    w3a
    #
    @16
    @20
    wb
    @4
    @23
    @12
    @6
    @4
    @3
    @21
    @22
    @1
    @2
    @3
    simp3
    #
    @4
    0zd
    @1
    @2
    @22
    @3
    @1
    @5
    cV
    cA
    lencl
    #
    nn0zd
    #
    3ad2ant1
    #
    3jca
    ad2antrl
    cI
    cc0
    @5
    elfzo
    syl
    mpbird
    @1
    @2
    @16
    df-3an
    sylanbrc
    @17
    @11
    @7
    cV
    cA
    cB
    cI
    ccatval1
    eqcomd
    syl
    ex
    @13
    @12
    wn
    #
    @14
    @4
    @28
    @14
    wi
    @6
    @4
    @28
    cI
    cc0
    clt
    wbr
    #
    @14
    @4
    cI
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    wa
    #
    @29
    @28
    wb
    @3
    @1
    @32
    @2
    @3
    @30
    @31
    cI
    zre
    #
    @3
    0red
    jca
    3ad2ant3
    cI
    cc0
    ltnle
    syl
    @4
    @29
    @14
    @4
    @29
    wa
    #
    @7
    c0
    @11
    @34
    @1
    @3
    wa
    #
    @29
    @5
    cI
    cle
    wbr
    #
    wo
    @7
    c0
    wceq
    @4
    @35
    @29
    @1
    @3
    @35
    @2
    @35
    id
    3adant2
    adantr
    @34
    @29
    @36
    @4
    @29
    simpr
    #
    orcd
    cI
    cV
    cA
    wrdsymb0
    sylc
    @34
    @10
    @0
    wcel
    #
    @3
    wa
    #
    @29
    @10
    chash
    cfv
    #
    cI
    cle
    wbr
    #
    wo
    #
    @11
    c0
    wceq
    #
    @4
    @39
    @29
    @4
    @38
    @3
    @1
    @2
    @38
    @3
    cV
    cA
    cB
    ccatcl
    3adant3
    @24
    jca
    #
    adantr
    @34
    @29
    @41
    @37
    orcd
    cI
    cV
    @10
    wrdsymb0
    #
    sylc
    eqtr4d
    ex
    sylbird
    adantr
    com12
    pm2.61i
    @4
    @6
    wn
    #
    wa
    #
    @11
    @9
    cI
    @5
    cB
    chash
    cfv
    #
    caddc
    co
    #
    clt
    wbr
    #
    @47
    @11
    @9
    wceq
    #
    wi
    @50
    @47
    @51
    @50
    @47
    wa
    #
    @1
    @2
    cI
    @5
    @49
    cfzo
    co
    wcel
    #
    w3a
    #
    @51
    @52
    @18
    @53
    @54
    @4
    @18
    @50
    @46
    @19
    ad2antrl
    @52
    @53
    @36
    @50
    wa
    #
    @52
    @50
    @36
    @47
    @36
    @50
    @4
    @36
    @46
    @1
    @3
    @36
    @46
    wb
    #
    @2
    @1
    @5
    cr
    wcel
    #
    @30
    @56
    @3
    @1
    @5
    @25
    nn0red
    #
    @33
    @5
    cI
    lenlt
    syl2an
    3adant2
    biimpar
    anim2i
    ancomd
    @52
    @3
    @22
    @49
    cz
    wcel
    #
    w3a
    #
    @53
    @55
    wb
    @4
    @60
    @50
    @46
    @4
    @3
    @22
    @59
    @24
    @27
    @1
    @2
    @59
    @3
    @1
    @22
    @48
    cz
    wcel
    @59
    @2
    @26
    @2
    @48
    cV
    cB
    lencl
    #
    nn0zd
    @5
    @48
    zaddcl
    syl2an
    3adant3
    3jca
    ad2antrl
    cI
    @5
    @49
    elfzo
    syl
    mpbird
    @1
    @2
    @53
    df-3an
    sylanbrc
    cV
    cA
    cB
    cI
    ccatval2
    syl
    ex
    @47
    @50
    wn
    #
    @51
    @4
    @62
    @51
    wi
    @46
    @4
    @62
    @49
    cI
    cle
    wbr
    #
    @51
    @4
    @49
    cI
    @1
    @2
    @49
    cr
    wcel
    #
    @3
    @1
    @57
    @48
    cr
    wcel
    #
    @64
    @2
    @58
    @2
    @48
    @61
    nn0red
    #
    @5
    @48
    readdcl
    syl2an
    3adant3
    @3
    @1
    @30
    @2
    @33
    3ad2ant3
    lenltd
    @4
    @63
    @51
    @4
    @63
    wa
    #
    @11
    c0
    @9
    @67
    @39
    @42
    @43
    @4
    @39
    @63
    @44
    adantr
    @67
    @41
    @29
    @67
    @40
    @49
    cI
    cle
    @4
    @40
    @49
    wceq
    #
    @63
    @1
    @2
    @68
    @3
    cV
    cA
    cB
    ccatlen
    3adant3
    adantr
    @4
    @63
    simpr
    eqbrtrd
    olcd
    @45
    sylc
    @67
    @2
    @8
    cz
    wcel
    #
    wa
    #
    @8
    cc0
    clt
    wbr
    #
    @48
    @8
    cle
    wbr
    #
    wo
    @9
    c0
    wceq
    @4
    @70
    @63
    @4
    @2
    @69
    @1
    @2
    @3
    simp2
    @1
    @3
    @69
    @2
    @3
    @1
    @69
    @1
    @3
    @22
    @69
    @26
    cI
    @5
    zsubcl
    sylan2
    ancoms
    3adant2
    jca
    adantr
    @67
    @72
    @71
    @4
    @63
    @72
    @1
    @57
    @2
    @65
    @3
    @30
    @63
    @72
    wb
    @58
    @66
    @33
    @5
    @48
    cI
    leaddsub2
    syl3an
    biimpa
    olcd
    @8
    cV
    cB
    wrdsymb0
    sylc
    eqtr4d
    ex
    sylbird
    adantr
    com12
    pm2.61i
    eqcomd
    ifeqda
    eqcomd
end
