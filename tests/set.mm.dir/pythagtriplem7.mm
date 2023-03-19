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
include "cz.mm"
include "cn0.mm"
include "cmul.mm"
include "simp3.mm"
include "nnzd.mm"
include "simp2.mm"
include "zsubcld.mm"
include "3ad2ant1.mm"
include "nnaddcld.mm"
include "nnnn0d.mm"
include "nnnn0.mm"
include "3jca.mm"
include "pythagtriplem4.mm"
include "oveq1d.mm"
include "nnz.mm"
include "1gcd.mm"
include "syl.mm"
include "eqtrd.mm"
include "jca.mm"
include "oveq1.mm"
include "3ad2ant2.mm"
include "cc.mm"
include "nncn.mm"
include "sqcld.mm"
include "nncnd.mm"
include "pncand.mm"
include "subsq.mm"
include "syl2anc.mm"
include "zcnd.mm"
include "mulcomd.mm"
include "3eqtr3d.mm"
include "coprimeprodsq2.mm"
include "sylc.mm"
include "fveq2d.mm"
include "gcdcld.mm"
include "nn0red.mm"
include "nn0ge0d.mm"
include "sqrtsqd.mm"

theorem pythagtriplem7
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. NN /\ B e. NN /\ C e. NN ) /\ ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) /\ ( ( A gcd B ) = 1 /\ -. 2 || A ) ) -> ( sqrt ` ( C + B ) ) = ( ( C + B ) gcd A ) )

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
    caddc
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
    cC
    cB
    cmin
    co
    #
    cz
    wcel
    #
    @11
    cn0
    wcel
    #
    cA
    cn0
    wcel
    #
    w3a
    #
    @14
    @11
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
    @14
    @11
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
    @15
    @16
    @17
    @3
    @8
    @15
    @9
    @3
    cC
    cB
    @3
    cC
    @0
    @1
    @2
    simp3
    #
    nnzd
    @3
    cB
    @0
    @1
    @2
    simp2
    #
    nnzd
    zsubcld
    #
    3ad2ant1
    @3
    @8
    @16
    @9
    @3
    @11
    @3
    cC
    cB
    @23
    @24
    nnaddcld
    #
    nnnn0d
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
    @27
    c1
    wceq
    @3
    @8
    @28
    @9
    @0
    @1
    @28
    @2
    cA
    nnz
    3ad2ant1
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
    @30
    @31
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
    @30
    @4
    wceq
    @9
    @3
    @4
    @5
    @3
    cA
    @0
    @1
    cA
    cc
    wcel
    @2
    cA
    nncn
    3ad2ant1
    sqcld
    @3
    cB
    @3
    cB
    @24
    nncnd
    #
    sqcld
    pncand
    3ad2ant1
    @3
    @8
    @31
    @22
    wceq
    @9
    @3
    @31
    @11
    @14
    cmul
    co
    #
    @22
    @3
    cC
    cc
    wcel
    cB
    cc
    wcel
    @31
    @33
    wceq
    @3
    cC
    @23
    nncnd
    @32
    cC
    cB
    subsq
    syl2anc
    @3
    @11
    @14
    @3
    @11
    @26
    nncnd
    @3
    @14
    @25
    zcnd
    mulcomd
    eqtrd
    3ad2ant1
    3eqtr3d
    @14
    @11
    cA
    coprimeprodsq2
    sylc
    fveq2d
    @10
    @12
    @10
    @12
    @10
    @11
    cA
    @3
    @8
    @11
    cz
    wcel
    @9
    @3
    @11
    @26
    nnzd
    3ad2ant1
    @29
    gcdcld
    #
    nn0red
    @10
    @12
    @34
    nn0ge0d
    sqrtsqd
    eqtrd
end
