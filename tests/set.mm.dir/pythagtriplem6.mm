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
include "cmin.mm"
include "csqrt.mm"
include "cfv.mm"
include "cn0.mm"
include "cz.mm"
include "cmul.mm"
include "cc0.mm"
include "clt.mm"
include "nnz.mm"
include "3ad2ant3.mm"
include "3ad2ant2.mm"
include "zsubcld.mm"
include "3ad2ant1.mm"
include "pythagtriplem10.mm"
include "3adant3.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "nnnn0d.mm"
include "simp3.mm"
include "simp2.mm"
include "nnaddcld.mm"
include "nnzd.mm"
include "nnnn0.mm"
include "3jca.mm"
include "pythagtriplem4.mm"
include "oveq1d.mm"
include "1gcd.mm"
include "syl.mm"
include "eqtrd.mm"
include "jca.mm"
include "oveq1.mm"
include "zcnd.mm"
include "sqcld.mm"
include "cc.mm"
include "nncn.mm"
include "pncand.mm"
include "subsq.mm"
include "syl2anc.mm"
include "nncnd.mm"
include "mulcomd.mm"
include "3eqtr3d.mm"
include "coprimeprodsq.mm"
include "sylc.mm"
include "fveq2d.mm"
include "gcdcld.mm"
include "nn0red.mm"
include "nn0ge0d.mm"
include "sqrtsqd.mm"

theorem pythagtriplem6
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. NN /\ B e. NN /\ C e. NN ) /\ ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) /\ ( ( A gcd B ) = 1 /\ -. 2 || A ) ) -> ( sqrt ` ( C - B ) ) = ( ( C - B ) gcd A ) )

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
    #
    cB
    c2
    cexp
    co
    #
    caddc
    co
    #
    cC
    c2
    cexp
    co
    #
    wceq
    #
    cA
    cB
    cgcd
    co
    c1
    wceq
    c2
    cA
    cdvds
    wbr
    wn
    wa
    #
    w3a
    #
    cC
    cB
    cmin
    co
    #
    csqrt
    cfv
    @11
    cA
    cgcd
    co
    #
    c2
    cexp
    co
    #
    csqrt
    cfv
    @12
    @10
    @11
    @13
    csqrt
    @10
    @11
    cn0
    wcel
    #
    cC
    cB
    caddc
    co
    #
    cz
    wcel
    #
    cA
    cn0
    wcel
    #
    w3a
    #
    @11
    @15
    cgcd
    co
    #
    cA
    cgcd
    co
    #
    c1
    wceq
    #
    wa
    @4
    @11
    @15
    cmul
    co
    #
    wceq
    @11
    @13
    wceq
    @10
    @18
    @21
    @10
    @14
    @16
    @17
    @10
    @11
    @10
    @11
    cz
    wcel
    #
    cc0
    @11
    clt
    wbr
    #
    @11
    cn
    wcel
    @3
    @8
    @23
    @9
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
    #
    @3
    @8
    @24
    @9
    cA
    cB
    cC
    pythagtriplem10
    3adant3
    @11
    elnnz
    sylanbrc
    nnnn0d
    @3
    @8
    @16
    @9
    @3
    @15
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
    @8
    @17
    @9
    @0
    @1
    @17
    @2
    cA
    nnnn0
    3ad2ant1
    3ad2ant1
    3jca
    @10
    @20
    c1
    cA
    cgcd
    co
    #
    c1
    @10
    @19
    c1
    cA
    cgcd
    cA
    cB
    cC
    pythagtriplem4
    oveq1d
    @10
    cA
    cz
    wcel
    #
    @28
    c1
    wceq
    @3
    @8
    @29
    @9
    @0
    @1
    @29
    @2
    cA
    nnz
    3ad2ant1
    #
    3ad2ant1
    #
    cA
    1gcd
    syl
    eqtrd
    jca
    @10
    @6
    @5
    cmin
    co
    #
    @7
    @5
    cmin
    co
    #
    @4
    @22
    @8
    @3
    @32
    @33
    wceq
    @9
    @6
    @7
    @5
    cmin
    oveq1
    3ad2ant2
    @3
    @8
    @32
    @4
    wceq
    @9
    @3
    @4
    @5
    @3
    cA
    @3
    cA
    @30
    zcnd
    sqcld
    @3
    cB
    @1
    @0
    cB
    cc
    wcel
    #
    @2
    cB
    nncn
    3ad2ant2
    #
    sqcld
    pncand
    3ad2ant1
    @3
    @8
    @33
    @22
    wceq
    @9
    @3
    @33
    @15
    @11
    cmul
    co
    #
    @22
    @3
    cC
    cc
    wcel
    #
    @34
    @33
    @36
    wceq
    @2
    @0
    @37
    @1
    cC
    nncn
    3ad2ant3
    @35
    cC
    cB
    subsq
    syl2anc
    @3
    @15
    @11
    @3
    @15
    @27
    nncnd
    @3
    @11
    @25
    zcnd
    mulcomd
    eqtrd
    3ad2ant1
    3eqtr3d
    @11
    @15
    cA
    coprimeprodsq
    sylc
    fveq2d
    @10
    @12
    @10
    @12
    @10
    @11
    cA
    @26
    @31
    gcdcld
    #
    nn0red
    @10
    @12
    @38
    nn0ge0d
    sqrtsqd
    eqtrd
end
