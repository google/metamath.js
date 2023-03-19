include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "c2.mm"
include "caddc.mm"
include "cfa.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cn.mm"
include "wo.mm"
include "elnn0.mm"
include "0exp.mm"
include "adantl.mm"
include "nnnn0.mm"
include "2nn0.mm"
include "nn0sqcl.mm"
include "nn0expcl.mm"
include "sylancr.mm"
include "nn0addcl.mm"
include "syldan.mm"
include "nn0mulcld.mm"
include "sylan2.mm"
include "nn0ge0d.mm"
include "eqbrtrd.mm"
include "1nn.mm"
include "0nn0.mm"
include "sylancl.mm"
include "nnexpcl.mm"
include "mpdan.mm"
include "id.mm"
include "oveq1.mm"
include "00id.mm"
include "syl6eq.mm"
include "oveq12d.mm"
include "0exp0e1.mm"
include "syl6eqel.mm"
include "jaoi.mm"
include "sylbi.mm"
include "nnmulcl.mm"
include "nnge1d.mm"
include "adantr.mm"
include "wb.mm"
include "oveq2.mm"
include "sq0i.mm"
include "oveq2d.mm"
include "cc.mm"
include "2cn.mm"
include "exp0.mm"
include "ax-mp.mm"
include "breq12d.mm"
include "mpbird.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "nn0cn.mm"
include "exp0d.mm"
include "mpan.mm"
include "nn0cnd.mm"
include "mulid1d.mm"
include "sylan9eq.mm"
include "3brtr4d.mm"
include "fveq2.mm"
include "fac0.mm"

theorem faclbnd4lem3
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( ( M e. NN0 /\ K e. NN0 ) /\ N = 0 ) -> ( ( N ^ K ) x. ( M ^ N ) ) <_ ( ( ( 2 ^ ( K ^ 2 ) ) x. ( M ^ ( M + K ) ) ) x. ( ! ` N ) ) )

  proof
    cM
    cn0
    wcel
    #
    cK
    cn0
    wcel
    #
    wa
    #
    cN
    cc0
    wceq
    #
    wa
    cN
    cK
    cexp
    co
    #
    cM
    cN
    cexp
    co
    #
    cmul
    co
    #
    c2
    cK
    c2
    cexp
    co
    #
    cexp
    co
    #
    cM
    cM
    cK
    caddc
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cN
    cfa
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    cc0
    cK
    cexp
    co
    #
    cM
    cc0
    cexp
    co
    #
    cmul
    co
    #
    @11
    c1
    cmul
    co
    #
    cle
    wbr
    #
    @2
    @19
    @3
    @2
    @15
    @11
    @17
    @18
    cle
    @1
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
    @15
    @11
    cle
    wbr
    #
    cK
    elnn0
    @0
    @20
    @22
    @21
    @0
    @20
    wa
    #
    @15
    cc0
    @11
    cle
    @20
    @15
    cc0
    wceq
    @0
    cK
    0exp
    adantl
    @23
    @11
    @20
    @0
    @1
    @11
    cn0
    wcel
    cK
    nnnn0
    @2
    @8
    @10
    @1
    @8
    cn0
    wcel
    #
    @0
    @1
    c2
    cn0
    wcel
    @7
    cn0
    wcel
    @24
    2nn0
    cK
    nn0sqcl
    c2
    @7
    nn0expcl
    sylancr
    adantl
    @0
    @1
    @9
    cn0
    wcel
    @10
    cn0
    wcel
    cM
    cK
    nn0addcl
    cM
    @9
    nn0expcl
    syldan
    nn0mulcld
    #
    sylan2
    nn0ge0d
    eqbrtrd
    @0
    @21
    wa
    @22
    c1
    c1
    cM
    cM
    cc0
    caddc
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    @0
    @29
    @21
    @0
    @28
    @0
    c1
    cn
    wcel
    @27
    cn
    wcel
    #
    @28
    cn
    wcel
    1nn
    @0
    cM
    cn
    wcel
    #
    cM
    cc0
    wceq
    #
    wo
    @30
    cM
    elnn0
    @31
    @30
    @32
    @31
    @26
    cn0
    wcel
    #
    @30
    @31
    @0
    cc0
    cn0
    wcel
    #
    @33
    cM
    nnnn0
    0nn0
    cM
    cc0
    nn0addcl
    sylancl
    cM
    @26
    nnexpcl
    mpdan
    @32
    @27
    c1
    cn
    @32
    @27
    cc0
    cc0
    cexp
    co
    #
    c1
    @32
    cM
    cc0
    @26
    cc0
    cexp
    @32
    id
    @32
    @26
    cc0
    cc0
    caddc
    co
    cc0
    cM
    cc0
    cc0
    caddc
    oveq1
    00id
    syl6eq
    oveq12d
    0exp0e1
    syl6eq
    1nn
    syl6eqel
    jaoi
    sylbi
    c1
    @27
    nnmulcl
    sylancr
    nnge1d
    adantr
    @21
    @22
    @29
    wb
    @0
    @21
    @15
    c1
    @11
    @28
    cle
    @21
    @15
    @35
    c1
    cK
    cc0
    cc0
    cexp
    oveq2
    0exp0e1
    syl6eq
    @21
    @8
    c1
    @10
    @27
    cmul
    @21
    @8
    c2
    cc0
    cexp
    co
    #
    c1
    @21
    @7
    cc0
    c2
    cexp
    cK
    sq0i
    oveq2d
    c2
    cc
    wcel
    @36
    c1
    wceq
    2cn
    c2
    exp0
    ax-mp
    syl6eq
    @21
    @9
    @26
    cM
    cexp
    cK
    cc0
    cM
    caddc
    oveq2
    oveq2d
    oveq12d
    breq12d
    adantl
    mpbird
    jaodan
    sylan2b
    @0
    @1
    @17
    @15
    c1
    cmul
    co
    @15
    @0
    @16
    c1
    @15
    cmul
    @0
    cM
    cM
    nn0cn
    exp0d
    oveq2d
    @1
    @15
    @1
    @15
    @34
    @1
    @15
    cn0
    wcel
    0nn0
    cc0
    cK
    nn0expcl
    mpan
    nn0cnd
    mulid1d
    sylan9eq
    @2
    @11
    @2
    @11
    @25
    nn0cnd
    mulid1d
    3brtr4d
    adantr
    @3
    @14
    @19
    wb
    @2
    @3
    @6
    @17
    @13
    @18
    cle
    @3
    @4
    @15
    @5
    @16
    cmul
    cN
    cc0
    cK
    cexp
    oveq1
    cN
    cc0
    cM
    cexp
    oveq2
    oveq12d
    @3
    @12
    c1
    @11
    cmul
    @3
    @12
    cc0
    cfa
    cfv
    c1
    cN
    cc0
    cfa
    fveq2
    fac0
    syl6eq
    oveq2d
    breq12d
    adantl
    mpbird
end
