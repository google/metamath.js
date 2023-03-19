include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "crmy.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cexp.mm"
include "crmx.mm"
include "cmin.mm"
include "cmul.mm"
include "cmo.mm"
include "wceq.mm"
include "clt.mm"
include "cdvds.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr.mm"
include "jm3.1lem2.mm"
include "cn0.mm"
include "eluzge2nn0.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "nnnn0d.mm"
include "jm2.18.mm"
include "syl3anc.mm"
include "cz.mm"
include "wb.mm"
include "simp1.mm"
include "nnz.mm"
include "3ad2ant3.mm"
include "frmx.mm"
include "fovcl.mm"
include "syl2anc.mm"
include "nn0zd.mm"
include "eluzelz.mm"
include "zsubcl.mm"
include "syl2an.mm"
include "3adant3.mm"
include "frmy.mm"
include "zmulcld.mm"
include "zsubcld.mm"
include "jm3.1lem3.mm"
include "nnnn0.mm"
include "nn0expcld.mm"
include "divalgmodcl.mm"
include "mpbir2and.mm"

theorem jm3.1
  let cA: class A
  let cK: class K
  let cN: class N


  assert |- ( ( ( A e. ( ZZ>= ` 2 ) /\ K e. ( ZZ>= ` 2 ) /\ N e. NN ) /\ ( K rmY ( N + 1 ) ) <_ A ) -> ( K ^ N ) = ( ( ( A rmX N ) - ( ( A - K ) x. ( A rmY N ) ) ) mod ( ( ( ( 2 x. A ) x. K ) - ( K ^ 2 ) ) - 1 ) ) )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cK
    @0
    wcel
    #
    cN
    cn
    wcel
    #
    w3a
    #
    cK
    cN
    c1
    caddc
    co
    crmy
    co
    cA
    cle
    wbr
    #
    wa
    #
    cK
    cN
    cexp
    co
    #
    cA
    cN
    crmx
    co
    #
    cA
    cK
    cmin
    co
    #
    cA
    cN
    crmy
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    c2
    cA
    cmul
    co
    cK
    cmul
    co
    cK
    c2
    cexp
    co
    cmin
    co
    c1
    cmin
    co
    #
    cmo
    co
    wceq
    #
    @7
    @13
    clt
    wbr
    #
    @13
    @12
    @7
    cmin
    co
    cdvds
    wbr
    #
    @6
    cA
    cK
    cN
    @1
    @2
    @3
    @5
    simpl1
    #
    @1
    @2
    @3
    @5
    simpl2
    #
    @1
    @2
    @3
    @5
    simpl3
    #
    @4
    @5
    simpr
    #
    jm3.1lem2
    @6
    @1
    cK
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    @16
    @17
    @4
    @21
    @5
    @2
    @1
    @21
    @3
    cK
    eluzge2nn0
    3ad2ant2
    #
    adantr
    @6
    cN
    @19
    nnnn0d
    cA
    cK
    cN
    jm2.18
    syl3anc
    @6
    @12
    cz
    wcel
    #
    @13
    cn
    wcel
    @7
    cn0
    wcel
    #
    @14
    @15
    @16
    wa
    wb
    @4
    @24
    @5
    @4
    @8
    @11
    @4
    @8
    @4
    @1
    cN
    cz
    wcel
    #
    @8
    cn0
    wcel
    @1
    @2
    @3
    simp1
    #
    @3
    @1
    @26
    @2
    cN
    nnz
    3ad2ant3
    #
    cA
    cN
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    syl2anc
    nn0zd
    @4
    @9
    @10
    @1
    @2
    @9
    cz
    wcel
    #
    @3
    @1
    cA
    cz
    wcel
    cK
    cz
    wcel
    @29
    @2
    c2
    cA
    eluzelz
    c2
    cK
    eluzelz
    cA
    cK
    zsubcl
    syl2an
    3adant3
    @4
    @1
    @26
    @10
    cz
    wcel
    @27
    @28
    cA
    cN
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    syl2anc
    zmulcld
    zsubcld
    adantr
    @6
    cA
    cK
    cN
    @17
    @18
    @19
    @20
    jm3.1lem3
    @4
    @25
    @5
    @4
    cK
    cN
    @23
    @3
    @1
    @22
    @2
    cN
    nnnn0
    3ad2ant3
    nn0expcld
    adantr
    @13
    @7
    @12
    divalgmodcl
    syl3anc
    mpbir2and
end
