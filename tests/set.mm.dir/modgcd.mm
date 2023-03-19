include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "cgcd.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cneg.mm"
include "cmul.mm"
include "caddc.mm"
include "cmin.mm"
include "cr.mm"
include "crp.mm"
include "wceq.mm"
include "zre.mm"
include "nnrp.mm"
include "modval.mm"
include "syl2an.mm"
include "cc.mm"
include "zcn.mm"
include "adantr.mm"
include "nncn.mm"
include "adantl.mm"
include "cc0.mm"
include "wne.mm"
include "nnre.mm"
include "nnne0.mm"
include "redivcl.mm"
include "syl3an.mm"
include "3anidm23.mm"
include "flcld.mm"
include "zcnd.mm"
include "w3a.mm"
include "mulneg1.mm"
include "mulcom.mm"
include "negeqd.mm"
include "eqtrd.mm"
include "ancoms.mm"
include "3adant1.mm"
include "oveq2d.mm"
include "mulcl.mm"
include "negsub.mm"
include "sylan2.mm"
include "3impb.mm"
include "syl3anc.mm"
include "eqtr4d.mm"
include "znegcld.mm"
include "nnz.mm"
include "simpl.mm"
include "gcdaddm.mm"
include "zmodcl.mm"
include "nn0zd.mm"
include "gcdcom.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"

theorem modgcd
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. NN ) -> ( ( M mod N ) gcd N ) = ( M gcd N ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cN
    cM
    cN
    cmo
    co
    #
    cgcd
    co
    #
    cN
    cM
    cgcd
    co
    #
    @3
    cN
    cgcd
    co
    #
    cM
    cN
    cgcd
    co
    #
    @2
    @4
    cN
    cM
    cM
    cN
    cdiv
    co
    #
    cfl
    cfv
    #
    cneg
    #
    cN
    cmul
    co
    #
    caddc
    co
    #
    cgcd
    co
    #
    @5
    @2
    @3
    @12
    cN
    cgcd
    @2
    @3
    cM
    cN
    @9
    cmul
    co
    #
    cmin
    co
    #
    @12
    @0
    cM
    cr
    wcel
    #
    cN
    crp
    wcel
    @3
    @15
    wceq
    @1
    cM
    zre
    #
    cN
    nnrp
    cM
    cN
    modval
    syl2an
    @2
    cM
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    @9
    cc
    wcel
    #
    @12
    @15
    wceq
    @0
    @18
    @1
    cM
    zcn
    adantr
    @1
    @19
    @0
    cN
    nncn
    adantl
    @2
    @9
    @2
    @8
    @0
    @1
    @8
    cr
    wcel
    #
    @0
    @16
    @1
    cN
    cr
    wcel
    @1
    cN
    cc0
    wne
    @21
    @17
    cN
    nnre
    cN
    nnne0
    cM
    cN
    redivcl
    syl3an
    3anidm23
    flcld
    #
    zcnd
    @18
    @19
    @20
    w3a
    #
    @12
    cM
    @14
    cneg
    #
    caddc
    co
    #
    @15
    @23
    @11
    @24
    cM
    caddc
    @19
    @20
    @11
    @24
    wceq
    #
    @18
    @20
    @19
    @26
    @20
    @19
    wa
    #
    @11
    @9
    cN
    cmul
    co
    #
    cneg
    @24
    @9
    cN
    mulneg1
    @27
    @28
    @14
    @9
    cN
    mulcom
    negeqd
    eqtrd
    ancoms
    3adant1
    oveq2d
    @18
    @19
    @20
    @25
    @15
    wceq
    #
    @19
    @20
    wa
    @18
    @14
    cc
    wcel
    @29
    cN
    @9
    mulcl
    cM
    @14
    negsub
    sylan2
    3impb
    eqtrd
    syl3anc
    eqtr4d
    oveq2d
    @2
    @10
    cz
    wcel
    cN
    cz
    wcel
    #
    @0
    @5
    @13
    wceq
    @2
    @9
    @22
    znegcld
    @1
    @30
    @0
    cN
    nnz
    adantl
    #
    @0
    @1
    simpl
    #
    @10
    cN
    cM
    gcdaddm
    syl3anc
    eqtr4d
    @2
    @30
    @3
    cz
    wcel
    @4
    @6
    wceq
    @31
    @2
    @3
    cM
    cN
    zmodcl
    nn0zd
    cN
    @3
    gcdcom
    syl2anc
    @2
    @30
    @0
    @5
    @7
    wceq
    @31
    @32
    cN
    cM
    gcdcom
    syl2anc
    3eqtr3d
end
