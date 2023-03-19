include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmul.mm"
include "cmo.mm"
include "wceq.mm"
include "cc0.mm"
include "wne.mm"
include "wb.mm"
include "nnz.mm"
include "adantl.mm"
include "zsubcl.mm"
include "3adant3.mm"
include "adantr.mm"
include "nnne0.mm"
include "jca.mm"
include "3ad2ant3.mm"
include "dvdscmulr.mm"
include "bicomd.mm"
include "syl3anc.mm"
include "cc.mm"
include "zcn.mm"
include "nncn.mm"
include "3anim123i.mm"
include "3anrot.mm"
include "sylibr.mm"
include "subdi.mm"
include "syl.mm"
include "breq2d.mm"
include "bitrd.mm"
include "simpr.mm"
include "simp1.mm"
include "simp2.mm"
include "moddvds.mm"
include "simpl3.mm"
include "nnmulcld.mm"
include "zmulcld.mm"
include "3bitr4d.mm"

theorem modmulconst
  let cA: class A
  let cB: class B
  let cC: class C
  let cM: class M


  assert |- ( ( ( A e. ZZ /\ B e. ZZ /\ C e. NN ) /\ M e. NN ) -> ( ( A mod M ) = ( B mod M ) <-> ( ( C x. A ) mod ( C x. M ) ) = ( ( C x. B ) mod ( C x. M ) ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cC
    cn
    wcel
    #
    w3a
    #
    cM
    cn
    wcel
    #
    wa
    #
    cM
    cA
    cB
    cmin
    co
    #
    cdvds
    wbr
    #
    cC
    cM
    cmul
    co
    #
    cC
    cA
    cmul
    co
    #
    cC
    cB
    cmul
    co
    #
    cmin
    co
    #
    cdvds
    wbr
    #
    cA
    cM
    cmo
    co
    cB
    cM
    cmo
    co
    wceq
    #
    @9
    @8
    cmo
    co
    @10
    @8
    cmo
    co
    wceq
    #
    @5
    @7
    @8
    cC
    @6
    cmul
    co
    #
    cdvds
    wbr
    #
    @12
    @5
    cM
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    cC
    cz
    wcel
    #
    cC
    cc0
    wne
    #
    wa
    #
    @7
    @16
    wb
    @4
    @17
    @3
    cM
    nnz
    adantl
    @3
    @18
    @4
    @0
    @1
    @18
    @2
    cA
    cB
    zsubcl
    3adant3
    adantr
    @3
    @21
    @4
    @2
    @0
    @21
    @1
    @2
    @19
    @20
    cC
    nnz
    #
    cC
    nnne0
    jca
    3ad2ant3
    adantr
    @17
    @18
    @21
    w3a
    @16
    @7
    cC
    cM
    @6
    dvdscmulr
    bicomd
    syl3anc
    @5
    @15
    @11
    @8
    cdvds
    @3
    @15
    @11
    wceq
    #
    @4
    @3
    cC
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    w3a
    #
    @23
    @3
    @25
    @26
    @24
    w3a
    @27
    @0
    @25
    @1
    @26
    @2
    @24
    cA
    zcn
    cB
    zcn
    cC
    nncn
    3anim123i
    @24
    @25
    @26
    3anrot
    sylibr
    cC
    cA
    cB
    subdi
    syl
    adantr
    breq2d
    bitrd
    @5
    @4
    @0
    @1
    @13
    @7
    wb
    @3
    @4
    simpr
    #
    @3
    @0
    @4
    @0
    @1
    @2
    simp1
    #
    adantr
    @3
    @1
    @4
    @0
    @1
    @2
    simp2
    #
    adantr
    cA
    cB
    cM
    moddvds
    syl3anc
    @5
    @8
    cn
    wcel
    @9
    cz
    wcel
    #
    @10
    cz
    wcel
    #
    @14
    @12
    wb
    @5
    cC
    cM
    @0
    @1
    @2
    @4
    simpl3
    @28
    nnmulcld
    @3
    @31
    @4
    @3
    cC
    cA
    @2
    @0
    @19
    @1
    @22
    3ad2ant3
    #
    @29
    zmulcld
    adantr
    @3
    @32
    @4
    @3
    cC
    cB
    @33
    @30
    zmulcld
    adantr
    @9
    @10
    @8
    moddvds
    syl3anc
    3bitr4d
end
