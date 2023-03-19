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
include "nnz.mm"
include "3ad2ant3.mm"
include "3ad2ant2.mm"
include "zaddcld.mm"
include "3ad2ant1.mm"
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
include "zsubcld.mm"
include "pythagtriplem6.mm"
include "opoe.mm"
include "syl22anc.mm"
include "nnaddcld.mm"
include "wne.mm"
include "2ne0.mm"
include "dvdsval2.mm"
include "mp3an12.mm"
include "syl.mm"
include "mpbid.mm"
include "nnred.mm"
include "nngt0d.mm"
include "addgt0d.mm"
include "cr.mm"
include "halfpos2.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "syl5eqel.mm"

theorem pythagtriplem11
  let cA: class A
  let cB: class B
  let cC: class C
  let cM: class M
  assume pythagtriplem11.1: |- M = ( ( ( sqrt ` ( C + B ) ) + ( sqrt ` ( C - B ) ) ) / 2 )


  assert |- ( ( ( A e. NN /\ B e. NN /\ C e. NN ) /\ ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) /\ ( ( A gcd B ) = 1 /\ -. 2 || A ) ) -> M e. NN )

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
    cM
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
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cn
    pythagtriplem11.1
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
    #
    @1
    @0
    cB
    cz
    wcel
    @2
    cB
    nnz
    3ad2ant2
    #
    zaddcld
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
    @36
    @6
    @24
    @9
    @36
    wa
    c2
    @12
    cdvds
    wbr
    #
    @6
    @9
    @37
    @6
    wa
    #
    @36
    @9
    @12
    cz
    wcel
    #
    @28
    @38
    @36
    wb
    #
    @3
    @4
    @39
    @8
    @3
    cC
    cB
    @30
    @31
    zsubcld
    3ad2ant1
    @32
    @33
    @39
    @28
    @40
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
    @35
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
    opoe
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
    @11
    @13
    @21
    @34
    nnaddcld
    #
    nnzd
    @33
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
    @11
    @13
    @9
    @11
    @21
    nnred
    @9
    @13
    @34
    nnred
    @9
    @11
    @21
    nngt0d
    @9
    @13
    @34
    nngt0d
    addgt0d
    @9
    @14
    cr
    wcel
    @44
    @17
    wb
    @9
    @14
    @43
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
