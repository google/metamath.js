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
include "oveq2.mm"
include "adantl.mm"
include "cz.mm"
include "nnz.mm"
include "zsqcl.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "gcdadd.mm"
include "syl2anc.mm"
include "gcdcom.mm"
include "eqtr3d.mm"
include "adantr.mm"
include "simpl2.mm"
include "simpl3.mm"
include "sqgcd.mm"
include "simpl1.mm"
include "3eqtr4d.mm"
include "3adant3.mm"
include "simp3l.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wb.mm"
include "3ad2ant3.mm"
include "gcdcld.mm"
include "nn0red.mm"
include "nn0ge0d.mm"
include "1re.mm"
include "0le1.mm"
include "sq11.mm"
include "mpanr12.mm"
include "mpbid.mm"

theorem pythagtriplem3
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. NN /\ B e. NN /\ C e. NN ) /\ ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) /\ ( ( A gcd B ) = 1 /\ -. 2 || A ) ) -> ( B gcd C ) = 1 )

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
    #
    c1
    wceq
    #
    c2
    cA
    cdvds
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cB
    cC
    cgcd
    co
    #
    c2
    cexp
    co
    #
    c1
    c2
    cexp
    co
    #
    wceq
    #
    @14
    c1
    wceq
    #
    @13
    @15
    @9
    c2
    cexp
    co
    #
    @16
    @3
    @8
    @15
    @19
    wceq
    @12
    @3
    @8
    wa
    #
    @5
    @7
    cgcd
    co
    #
    @4
    @5
    cgcd
    co
    #
    @15
    @19
    @20
    @5
    @6
    cgcd
    co
    #
    @21
    @22
    @8
    @23
    @21
    wceq
    @3
    @6
    @7
    @5
    cgcd
    oveq2
    adantl
    @3
    @23
    @22
    wceq
    @8
    @3
    @5
    @4
    cgcd
    co
    #
    @23
    @22
    @3
    @5
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @24
    @23
    wceq
    @1
    @0
    @25
    @2
    @1
    cB
    cz
    wcel
    #
    @25
    cB
    nnz
    #
    cB
    zsqcl
    syl
    3ad2ant2
    #
    @0
    @1
    @26
    @2
    @0
    cA
    cz
    wcel
    @26
    cA
    nnz
    cA
    zsqcl
    syl
    3ad2ant1
    #
    @5
    @4
    gcdadd
    syl2anc
    @3
    @25
    @26
    @24
    @22
    wceq
    @29
    @30
    @5
    @4
    gcdcom
    syl2anc
    eqtr3d
    adantr
    eqtr3d
    @20
    @1
    @2
    @15
    @21
    wceq
    @0
    @1
    @2
    @8
    simpl2
    #
    @0
    @1
    @2
    @8
    simpl3
    cB
    cC
    sqgcd
    syl2anc
    @20
    @0
    @1
    @19
    @22
    wceq
    @0
    @1
    @2
    @8
    simpl1
    @31
    cA
    cB
    sqgcd
    syl2anc
    3eqtr4d
    3adant3
    @13
    @9
    c1
    c2
    cexp
    @3
    @8
    @10
    @11
    simp3l
    oveq1d
    eqtrd
    @13
    @14
    cr
    wcel
    #
    cc0
    @14
    cle
    wbr
    #
    @17
    @18
    wb
    #
    @3
    @8
    @32
    @12
    @3
    @14
    @3
    cB
    cC
    @1
    @0
    @27
    @2
    @28
    3ad2ant2
    @2
    @0
    cC
    cz
    wcel
    @1
    cC
    nnz
    3ad2ant3
    gcdcld
    #
    nn0red
    3ad2ant1
    @3
    @8
    @33
    @12
    @3
    @14
    @35
    nn0ge0d
    3ad2ant1
    @32
    @33
    wa
    c1
    cr
    wcel
    cc0
    c1
    cle
    wbr
    @34
    1re
    0le1
    @14
    c1
    sq11
    mpanr12
    syl2anc
    mpbid
end
