include "cn.mm"
include "wcel.mm"
include "w3a.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cgcd.mm"
include "c1.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "csqrt.mm"
include "cfv.mm"
include "cmin.mm"
include "cdiv.mm"
include "cz.mm"
include "cc0.mm"
include "clt.mm"
include "pythagtriplem9.mm"
include "nnzd.mm"
include "simp3r.mm"
include "wb.mm"
include "simp3.mm"
include "simp2.mm"
include "nnaddcld.mm"
include "3ad2ant1.mm"
include "nnz.mm"
include "2z.mm"
include "dvdsgcdb.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "biimpar.mm"
include "simprd.mm"
include "mtand.mm"
include "pythagtriplem7.mm"
include "breq2d.mm"
include "mtbird.mm"
include "pythagtriplem8.mm"
include "3ad2ant3.mm"
include "3ad2ant2.mm"
include "zsubcld.mm"
include "pythagtriplem6.mm"
include "omoe.mm"
include "syl22anc.mm"
include "cr.mm"
include "zred.mm"
include "simp13.mm"
include "nnred.mm"
include "crp.mm"
include "nnrp.mm"
include "ltsubrpd.mm"
include "nngt0.mm"
include "simp12.mm"
include "ltaddposd.mm"
include "mpbid.mm"
include "lttrd.mm"
include "cle.mm"
include "pythagtriplem10.mm"
include "3adant3.mm"
include "wi.mm"
include "0re.mm"
include "ltle.mm"
include "mpan.mm"
include "sylc.mm"
include "addgt0d.mm"
include "sqrtltd.mm"
include "nnsub.mm"
include "wne.mm"
include "2ne0.mm"
include "dvdsval2.mm"
include "mp3an12.mm"
include "syl.mm"
include "nngt0d.mm"
include "halfpos2.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "syl5eqel.mm"

theorem pythagtriplem13
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N
  assume pythagtriplem13.1: |- N = ( ( ( sqrt ` ( C + B ) ) - ( sqrt ` ( C - B ) ) ) / 2 )


  assert |- ( ( ( A e. NN /\ B e. NN /\ C e. NN ) /\ ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) /\ ( ( A gcd B ) = 1 /\ -. 2 || A ) ) -> N e. NN )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    cC
    cn
    wcel
    #
    w3a
    #
    cA
    c2
    cexp
    co
    cB
    c2
    cexp
    co
    caddc
    co
    cC
    c2
    cexp
    co
    wceq
    #
    cA
    cB
    cgcd
    co
    c1
    wceq
    #
    c2
    cA
    cdvds
    wbr
    #
    wn
    #
    wa
    #
    w3a
    #
    cN
    cC
    cB
    caddc
    co
    #
    csqrt
    cfv
    #
    cC
    cB
    cmin
    co
    #
    csqrt
    cfv
    #
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cn
    pythagtriplem13.1
    @9
    @15
    cz
    wcel
    #
    cc0
    @15
    clt
    wbr
    #
    @15
    cn
    wcel
    @9
    c2
    @14
    cdvds
    wbr
    #
    @16
    @9
    @11
    cz
    wcel
    c2
    @11
    cdvds
    wbr
    #
    wn
    @13
    cz
    wcel
    c2
    @13
    cdvds
    wbr
    #
    wn
    @18
    @9
    @11
    cA
    cB
    cC
    pythagtriplem9
    #
    nnzd
    @9
    @19
    c2
    @10
    cA
    cgcd
    co
    #
    cdvds
    wbr
    #
    @9
    @23
    @6
    @3
    @4
    @5
    @7
    simp3r
    #
    @9
    @23
    wa
    c2
    @10
    cdvds
    wbr
    #
    @6
    @9
    @25
    @6
    wa
    #
    @23
    @9
    @10
    cz
    wcel
    #
    cA
    cz
    wcel
    #
    @26
    @23
    wb
    #
    @3
    @4
    @27
    @8
    @3
    @10
    @3
    cC
    cB
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    simp2
    nnaddcld
    #
    nnzd
    3ad2ant1
    @3
    @4
    @28
    @8
    @0
    @1
    @28
    @2
    cA
    nnz
    3ad2ant1
    3ad2ant1
    #
    c2
    cz
    wcel
    #
    @27
    @28
    @29
    2z
    c2
    @10
    cA
    dvdsgcdb
    mp3an1
    syl2anc
    biimpar
    simprd
    mtand
    @9
    @11
    @22
    c2
    cdvds
    cA
    cB
    cC
    pythagtriplem7
    breq2d
    mtbird
    @9
    @13
    cA
    cB
    cC
    pythagtriplem8
    #
    nnzd
    @9
    @20
    c2
    @12
    cA
    cgcd
    co
    #
    cdvds
    wbr
    #
    @9
    @35
    @6
    @24
    @9
    @35
    wa
    c2
    @12
    cdvds
    wbr
    #
    @6
    @9
    @36
    @6
    wa
    #
    @35
    @9
    @12
    cz
    wcel
    #
    @28
    @37
    @35
    wb
    #
    @3
    @4
    @38
    @8
    @3
    cC
    cB
    @2
    @0
    cC
    cz
    wcel
    @1
    cC
    nnz
    3ad2ant3
    @1
    @0
    cB
    cz
    wcel
    @2
    cB
    nnz
    3ad2ant2
    zsubcld
    #
    3ad2ant1
    @31
    @32
    @38
    @28
    @39
    2z
    c2
    @12
    cA
    dvdsgcdb
    mp3an1
    syl2anc
    biimpar
    simprd
    mtand
    @9
    @13
    @34
    c2
    cdvds
    cA
    cB
    cC
    pythagtriplem6
    breq2d
    mtbird
    @11
    @13
    omoe
    syl22anc
    @9
    @14
    cz
    wcel
    #
    @18
    @16
    wb
    #
    @9
    @14
    @9
    @13
    @11
    clt
    wbr
    #
    @14
    cn
    wcel
    #
    @9
    @12
    @10
    clt
    wbr
    @43
    @9
    @12
    cC
    @10
    @3
    @4
    @12
    cr
    wcel
    #
    @8
    @3
    @12
    @40
    zred
    3ad2ant1
    #
    @9
    cC
    @0
    @1
    @2
    @4
    @8
    simp13
    nnred
    #
    @3
    @4
    @10
    cr
    wcel
    #
    @8
    @3
    @10
    @30
    nnred
    3ad2ant1
    #
    @9
    cC
    cB
    @47
    @3
    @4
    cB
    crp
    wcel
    #
    @8
    @1
    @0
    @50
    @2
    cB
    nnrp
    3ad2ant2
    3ad2ant1
    ltsubrpd
    @9
    cc0
    cB
    clt
    wbr
    #
    cC
    @10
    clt
    wbr
    @3
    @4
    @51
    @8
    @1
    @0
    @51
    @2
    cB
    nngt0
    3ad2ant2
    3ad2ant1
    #
    @9
    cB
    cC
    @9
    cB
    @0
    @1
    @2
    @4
    @8
    simp12
    nnred
    #
    @47
    ltaddposd
    mpbid
    lttrd
    @9
    @12
    @10
    @46
    @9
    @45
    cc0
    @12
    clt
    wbr
    #
    cc0
    @12
    cle
    wbr
    #
    @46
    @3
    @4
    @54
    @8
    cA
    cB
    cC
    pythagtriplem10
    3adant3
    cc0
    cr
    wcel
    #
    @45
    @54
    @55
    wi
    0re
    cc0
    @12
    ltle
    mpan
    sylc
    @49
    @9
    @48
    cc0
    @10
    clt
    wbr
    #
    cc0
    @10
    cle
    wbr
    #
    @49
    @9
    cC
    cB
    @47
    @53
    @3
    @4
    cc0
    cC
    clt
    wbr
    #
    @8
    @2
    @0
    @59
    @1
    cC
    nngt0
    3ad2ant3
    3ad2ant1
    @52
    addgt0d
    @56
    @48
    @57
    @58
    wi
    0re
    cc0
    @10
    ltle
    mpan
    sylc
    sqrtltd
    mpbid
    @9
    @13
    cn
    wcel
    @11
    cn
    wcel
    @43
    @44
    wb
    @33
    @21
    @13
    @11
    nnsub
    syl2anc
    mpbid
    #
    nnzd
    @32
    c2
    cc0
    wne
    @41
    @42
    2z
    2ne0
    c2
    @14
    dvdsval2
    mp3an12
    syl
    mpbid
    @9
    cc0
    @14
    clt
    wbr
    #
    @17
    @9
    @14
    @60
    nngt0d
    @9
    @14
    cr
    wcel
    @61
    @17
    wb
    @9
    @14
    @60
    nnred
    @14
    halfpos2
    syl
    mpbid
    @15
    elnnz
    sylanbrc
    syl5eqel
end
