include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "crmy.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "crmx.mm"
include "cmul.mm"
include "caddc.mm"
include "cgcd.mm"
include "c1.mm"
include "wceq.mm"
include "wb.mm"
include "frmy.mm"
include "fovcl.mm"
include "3adant3.mm"
include "3adant2.mm"
include "cn0.mm"
include "frmx.mm"
include "nn0zd.mm"
include "gcdcom.mm"
include "syl2anc.mm"
include "jm2.19lem1.mm"
include "eqtrd.mm"
include "coprmdvdsb.mm"
include "syl112anc.mm"
include "nn0cnd.mm"
include "zcnd.mm"
include "mulcomd.mm"
include "breq2d.mm"
include "bitrd.mm"
include "zmulcld.mm"
include "dvdsmul2.mm"
include "dvdsadd2b.mm"
include "rmyadd.mm"
include "3com23.mm"
include "mulcld.mm"
include "addcomd.mm"
include "eqtr2d.mm"
include "3bitrd.mm"

theorem jm2.19lem2
  let cA: class A
  let cM: class M
  let cN: class N


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) -> ( ( A rmY M ) || ( A rmY N ) <-> ( A rmY M ) || ( A rmY ( N + M ) ) ) )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cA
    cM
    crmy
    co
    #
    cA
    cN
    crmy
    co
    #
    cdvds
    wbr
    #
    @5
    @6
    cA
    cM
    crmx
    co
    #
    cmul
    co
    #
    cdvds
    wbr
    #
    @5
    cA
    cN
    crmx
    co
    #
    @5
    cmul
    co
    #
    @9
    caddc
    co
    #
    cdvds
    wbr
    #
    @5
    cA
    cN
    cM
    caddc
    co
    crmy
    co
    #
    cdvds
    wbr
    @4
    @7
    @5
    @8
    @6
    cmul
    co
    #
    cdvds
    wbr
    #
    @10
    @4
    @5
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    @8
    cz
    wcel
    #
    @5
    @8
    cgcd
    co
    #
    c1
    wceq
    @7
    @17
    wb
    @1
    @2
    @18
    @3
    cA
    cM
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    3adant3
    #
    @1
    @3
    @19
    @2
    cA
    cN
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    3adant2
    #
    @4
    @8
    @1
    @2
    @8
    cn0
    wcel
    @3
    cA
    cM
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    3adant3
    #
    nn0zd
    #
    @4
    @21
    @8
    @5
    cgcd
    co
    #
    c1
    @4
    @18
    @20
    @21
    @26
    wceq
    @22
    @25
    @5
    @8
    gcdcom
    syl2anc
    @1
    @2
    @26
    c1
    wceq
    @3
    cA
    cM
    jm2.19lem1
    3adant3
    eqtrd
    @5
    @8
    @6
    coprmdvdsb
    syl112anc
    @4
    @16
    @9
    @5
    cdvds
    @4
    @8
    @6
    @4
    @8
    @24
    nn0cnd
    #
    @4
    @6
    @23
    zcnd
    #
    mulcomd
    breq2d
    bitrd
    @4
    @18
    @9
    cz
    wcel
    @12
    cz
    wcel
    @5
    @12
    cdvds
    wbr
    #
    @10
    @14
    wb
    @22
    @4
    @6
    @8
    @23
    @25
    zmulcld
    @4
    @11
    @5
    @4
    @11
    @1
    @3
    @11
    cn0
    wcel
    @2
    cA
    cN
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    3adant2
    #
    nn0zd
    #
    @22
    zmulcld
    @4
    @11
    cz
    wcel
    @18
    @29
    @31
    @22
    @11
    @5
    dvdsmul2
    syl2anc
    @5
    @9
    @12
    dvdsadd2b
    syl112anc
    @4
    @13
    @15
    @5
    cdvds
    @4
    @15
    @9
    @12
    caddc
    co
    #
    @13
    @1
    @3
    @2
    @15
    @32
    wceq
    cA
    cN
    cM
    rmyadd
    3com23
    @4
    @9
    @12
    @4
    @6
    @8
    @28
    @27
    mulcld
    @4
    @11
    @5
    @4
    @11
    @30
    nn0cnd
    @4
    @5
    @22
    zcnd
    mulcld
    addcomd
    eqtr2d
    breq2d
    3bitrd
end
