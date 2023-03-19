include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cconcat.mm"
include "cop.mm"
include "csubstr.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "cif.mm"
include "wceq.mm"
include "cn0.mm"
include "elfznn0.mm"
include "0elfz.mm"
include "syl.mm"
include "ancri.mm"
include "swrdccat3.mm"
include "imp.mm"
include "sylan2.mm"
include "iftrue.mm"
include "adantl.mm"
include "wn.mm"
include "w3a.mm"
include "iffalse.mm"
include "3ad2ant2.mm"
include "wi.mm"
include "wb.mm"
include "lencl.mm"
include "syl5eqel.mm"
include "nn0le0eq0.mm"
include "biimpd.mm"
include "adantr.mm"
include "c0.mm"
include "eqeq1i.mm"
include "biimpi.mm"
include "hasheq0.mm"
include "syl5ib.mm"
include "0m0e0.mm"
include "oveq2.mm"
include "eqcoms.mm"
include "syl5eqr.mm"
include "opeq1d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "swrdcl.mm"
include "ccatlid.mm"
include "eqtrd.mm"
include "ex.mm"
include "syld.mm"
include "3adant2.mm"
include "opeq2i.mm"
include "oveq2i.mm"
include "swrdid.mm"
include "syl5req.mm"
include "3ad2ant1.mm"
include "oveq1d.mm"
include "2if2.mm"
include "eqtr4d.mm"

theorem swrdccat3a
  let cA: class A
  let cB: class B
  let cL: class L
  let cN: class N
  let cV: class V
  let vk: setvar k
  let cM: class M
  assume swrdccatin12.l: |- L = ( # ` A )


  assert |- ( ( A e. Word V /\ B e. Word V ) -> ( N e. ( 0 ... ( L + ( # ` B ) ) ) -> ( ( A ++ B ) substr <. 0 , N >. ) = if ( N <_ L , ( A substr <. 0 , N >. ) , ( A ++ ( B substr <. 0 , ( N - L ) >. ) ) ) ) )

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
    wa
    #
    cN
    cc0
    cL
    cB
    chash
    cfv
    caddc
    co
    #
    cfz
    co
    wcel
    #
    cA
    cB
    cconcat
    co
    cc0
    cN
    cop
    #
    csubstr
    co
    #
    cN
    cL
    cle
    wbr
    #
    cA
    @6
    csubstr
    co
    #
    cA
    cB
    cc0
    cN
    cL
    cmin
    co
    #
    cop
    #
    csubstr
    co
    #
    cconcat
    co
    #
    cif
    #
    wceq
    @3
    @5
    wa
    #
    @7
    @8
    @9
    cL
    cc0
    cle
    wbr
    #
    cB
    cc0
    cL
    cmin
    co
    #
    @10
    cop
    #
    csubstr
    co
    #
    cA
    cc0
    cL
    cop
    #
    csubstr
    co
    #
    @12
    cconcat
    co
    #
    cif
    cif
    #
    @14
    @5
    @3
    cc0
    cc0
    cN
    cfz
    co
    wcel
    #
    @5
    wa
    #
    @7
    @23
    wceq
    #
    @5
    @24
    @5
    cN
    cn0
    wcel
    @24
    cN
    @4
    elfznn0
    cN
    0elfz
    syl
    ancri
    @3
    @25
    @26
    cA
    cB
    cL
    cc0
    cN
    cV
    swrdccatin12.l
    swrdccat3
    imp
    sylan2
    @15
    @8
    @16
    @9
    @19
    @22
    @14
    @8
    @14
    @9
    wceq
    @15
    @8
    @9
    @13
    iftrue
    adantl
    @15
    @8
    wn
    #
    @16
    w3a
    @14
    @13
    @19
    @27
    @15
    @14
    @13
    wceq
    #
    @16
    @8
    @9
    @13
    iffalse
    #
    3ad2ant2
    @15
    @16
    @13
    @19
    wceq
    #
    @27
    @15
    @16
    @30
    @3
    @16
    @30
    wi
    @5
    @3
    @16
    cL
    cc0
    wceq
    #
    @30
    @1
    @16
    @31
    wi
    @2
    @1
    @16
    @31
    @1
    cL
    cn0
    wcel
    @16
    @31
    wb
    @1
    cL
    cA
    chash
    cfv
    #
    cn0
    swrdccatin12.l
    cV
    cA
    lencl
    syl5eqel
    cL
    nn0le0eq0
    syl
    biimpd
    adantr
    @3
    @31
    @30
    @3
    @31
    wa
    #
    @13
    c0
    @19
    cconcat
    co
    #
    @19
    @33
    cA
    c0
    @12
    @19
    cconcat
    @3
    @31
    cA
    c0
    wceq
    #
    @1
    @31
    @35
    wi
    @2
    @31
    @32
    cc0
    wceq
    #
    @1
    @35
    @31
    @36
    cL
    @32
    cc0
    swrdccatin12.l
    eqeq1i
    biimpi
    cA
    @0
    hasheq0
    syl5ib
    adantr
    imp
    @33
    @11
    @18
    cB
    csubstr
    @33
    cc0
    @17
    @10
    @31
    cc0
    @17
    wceq
    @3
    @31
    cc0
    cc0
    cc0
    cmin
    co
    #
    @17
    0m0e0
    @37
    @17
    wceq
    cc0
    cL
    cc0
    cL
    cc0
    cmin
    oveq2
    eqcoms
    syl5eqr
    adantl
    opeq1d
    oveq2d
    oveq12d
    @3
    @34
    @19
    wceq
    #
    @31
    @2
    @38
    @1
    @2
    @19
    @0
    wcel
    @38
    cV
    cB
    @17
    @10
    swrdcl
    cV
    @19
    ccatlid
    syl
    adantl
    adantr
    eqtrd
    ex
    syld
    adantr
    imp
    3adant2
    eqtrd
    @15
    @27
    @16
    wn
    #
    w3a
    #
    @14
    @13
    @22
    @27
    @15
    @28
    @39
    @29
    3ad2ant2
    @40
    cA
    @21
    @12
    cconcat
    @15
    @27
    cA
    @21
    wceq
    #
    @39
    @3
    @41
    @5
    @1
    @41
    @2
    @1
    @21
    cA
    cc0
    @32
    cop
    #
    csubstr
    co
    cA
    @20
    @42
    cA
    csubstr
    cL
    @32
    cc0
    swrdccatin12.l
    opeq2i
    oveq2i
    cV
    cA
    swrdid
    syl5req
    adantr
    adantr
    3ad2ant1
    oveq1d
    eqtrd
    2if2
    eqtr4d
    ex
end
