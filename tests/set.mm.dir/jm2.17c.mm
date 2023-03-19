include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "crmy.mm"
include "cmin.mm"
include "cexp.mm"
include "clt.mm"
include "cr.mm"
include "2re.mm"
include "eluzelre.mm"
include "adantr.mm"
include "remulcl.mm"
include "sylancr.mm"
include "cz.mm"
include "nnz.mm"
include "adantl.mm"
include "peano2zd.mm"
include "frmy.mm"
include "fovcl.mm"
include "zred.mm"
include "syldan.mm"
include "remulcld.mm"
include "cc.mm"
include "wceq.mm"
include "nncn.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "sylan2.mm"
include "eqeltrd.mm"
include "resubcld.mm"
include "cn0.mm"
include "nnnn0.mm"
include "reexpcld.mm"
include "cc0.mm"
include "wbr.mm"
include "rmy0.mm"
include "nngt0.mm"
include "wb.mm"
include "simpl.mm"
include "0zd.mm"
include "ltrmy.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "eqbrtrrd.mm"
include "breqtrrd.mm"
include "ltsubposd.mm"
include "cle.mm"
include "jm2.17b.mm"
include "2nn.mm"
include "eluz2nn.mm"
include "nnmulcl.mm"
include "nngt0d.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "ltletrd.mm"
include "rmyluc2.mm"
include "recnd.mm"
include "expp1d.mm"
include "mulcomd.mm"
include "eqtrd.mm"
include "3brtr4d.mm"

theorem jm2.17c
  let cA: class A
  let cN: class N


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN ) -> ( A rmY ( ( N + 1 ) + 1 ) ) < ( ( 2 x. A ) ^ ( N + 1 ) ) )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    c2
    cA
    cmul
    co
    #
    cA
    cN
    c1
    caddc
    co
    #
    crmy
    co
    #
    cmul
    co
    #
    cA
    @5
    c1
    cmin
    co
    #
    crmy
    co
    #
    cmin
    co
    #
    @4
    @4
    cN
    cexp
    co
    #
    cmul
    co
    #
    cA
    @5
    c1
    caddc
    co
    crmy
    co
    #
    @4
    @5
    cexp
    co
    #
    clt
    @3
    @10
    @7
    @12
    @3
    @7
    @9
    @3
    @4
    @6
    @3
    c2
    cr
    wcel
    cA
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    2re
    @1
    @15
    @2
    c2
    cA
    eluzelre
    adantr
    c2
    cA
    remulcl
    sylancr
    #
    @1
    @2
    @5
    cz
    wcel
    #
    @6
    cr
    wcel
    #
    @3
    cN
    @2
    cN
    cz
    wcel
    #
    @1
    cN
    nnz
    #
    adantl
    #
    peano2zd
    #
    @1
    @18
    wa
    @6
    cA
    @5
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    zred
    syldan
    #
    remulcld
    #
    @3
    @9
    cA
    cN
    crmy
    co
    #
    cr
    @3
    @8
    cN
    cA
    crmy
    @3
    cN
    cc
    wcel
    #
    c1
    cc
    wcel
    @8
    cN
    wceq
    @2
    @27
    @1
    cN
    nncn
    adantl
    ax-1cn
    cN
    c1
    pncan
    sylancl
    oveq2d
    #
    @2
    @1
    @20
    @26
    cr
    wcel
    @21
    @1
    @20
    wa
    @26
    cA
    cN
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    zred
    sylan2
    eqeltrd
    #
    resubcld
    @25
    @3
    @4
    @11
    @17
    @3
    @4
    cN
    @17
    @2
    cN
    cn0
    wcel
    #
    @1
    cN
    nnnn0
    #
    adantl
    #
    reexpcld
    #
    remulcld
    @3
    cc0
    @9
    clt
    wbr
    @10
    @7
    clt
    wbr
    @3
    cc0
    @26
    @9
    clt
    @3
    cA
    cc0
    crmy
    co
    #
    cc0
    @26
    clt
    @1
    @34
    cc0
    wceq
    @2
    cA
    rmy0
    adantr
    @3
    cc0
    cN
    clt
    wbr
    #
    @34
    @26
    clt
    wbr
    #
    @2
    @35
    @1
    cN
    nngt0
    adantl
    @3
    @1
    cc0
    cz
    wcel
    @20
    @35
    @36
    wb
    @1
    @2
    simpl
    @3
    0zd
    @22
    cA
    cc0
    cN
    ltrmy
    syl3anc
    mpbid
    eqbrtrrd
    @28
    breqtrrd
    @3
    @9
    @7
    @29
    @25
    ltsubposd
    mpbid
    @3
    @6
    @11
    cle
    wbr
    #
    @7
    @12
    cle
    wbr
    #
    @2
    @1
    @30
    @37
    @31
    cA
    cN
    jm2.17b
    sylan2
    @3
    @19
    @11
    cr
    wcel
    @16
    cc0
    @4
    clt
    wbr
    #
    @37
    @38
    wb
    @24
    @33
    @17
    @1
    @39
    @2
    @1
    @4
    @1
    c2
    cn
    wcel
    cA
    cn
    wcel
    @4
    cn
    wcel
    2nn
    cA
    eluz2nn
    c2
    cA
    nnmulcl
    sylancr
    nngt0d
    adantr
    @6
    @11
    @4
    lemul2
    syl112anc
    mpbid
    ltletrd
    @1
    @2
    @18
    @13
    @10
    wceq
    @23
    cA
    @5
    rmyluc2
    syldan
    @3
    @14
    @11
    @4
    cmul
    co
    @12
    @3
    @4
    cN
    @3
    @4
    @17
    recnd
    #
    @32
    expp1d
    @3
    @11
    @4
    @3
    @11
    @33
    recnd
    @40
    mulcomd
    eqtrd
    3brtr4d
end
