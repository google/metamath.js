include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "cle.mm"
include "simpl1.mm"
include "simpl2.mm"
include "gcddvds.mm"
include "syl2anc.mm"
include "simpld.mm"
include "simprd.mm"
include "simprr.mm"
include "wi.mm"
include "cc0.mm"
include "wn.mm"
include "cn.mm"
include "wne.mm"
include "ax-1ne0.mm"
include "simprl.mm"
include "neeq1d.mm"
include "mpbiri.mm"
include "neneqd.mm"
include "simplrr.mm"
include "eqbrtrrd.mm"
include "wb.mm"
include "simpll3.mm"
include "0dvds.mm"
include "syl.mm"
include "mpbid.mm"
include "jca.mm"
include "ex.mm"
include "simpl3.mm"
include "gcdeq0.mm"
include "sylibrd.mm"
include "mtod.mm"
include "gcdn0cl.mm"
include "syl21anc.mm"
include "nnzd.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "mtbid.mm"
include "dvdslegcd.mm"
include "syl31anc.mm"
include "breqtrd.mm"
include "nnle1eq1.mm"

theorem rpdvds
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) /\ ( ( K gcd N ) = 1 /\ M || N ) ) -> ( K gcd M ) = 1 )

  proof
    cK
    cz
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
    cK
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    cM
    cN
    cdvds
    wbr
    #
    wa
    #
    wa
    #
    cK
    cM
    cgcd
    co
    #
    c1
    cle
    wbr
    #
    @9
    c1
    wceq
    #
    @8
    @9
    @4
    c1
    cle
    @8
    @9
    cK
    cdvds
    wbr
    #
    @9
    cN
    cdvds
    wbr
    #
    @9
    @4
    cle
    wbr
    #
    @8
    @12
    @9
    cM
    cdvds
    wbr
    #
    @8
    @0
    @1
    @12
    @15
    wa
    @0
    @1
    @2
    @7
    simpl1
    #
    @0
    @1
    @2
    @7
    simpl2
    #
    cK
    cM
    gcddvds
    syl2anc
    #
    simpld
    @8
    @15
    @6
    @13
    @8
    @12
    @15
    @18
    simprd
    @3
    @5
    @6
    simprr
    @8
    @9
    cz
    wcel
    #
    @1
    @2
    @15
    @6
    wa
    @13
    wi
    @8
    @9
    @8
    @0
    @1
    cK
    cc0
    wceq
    #
    cM
    cc0
    wceq
    #
    wa
    #
    wn
    @9
    cn
    wcel
    #
    @16
    @17
    @8
    @22
    @4
    cc0
    wceq
    #
    @8
    @4
    cc0
    @8
    @4
    cc0
    wne
    c1
    cc0
    wne
    ax-1ne0
    @8
    @4
    c1
    cc0
    @3
    @5
    @6
    simprl
    #
    neeq1d
    mpbiri
    neneqd
    #
    @8
    @22
    @20
    cN
    cc0
    wceq
    #
    wa
    #
    @24
    @8
    @22
    @28
    @8
    @22
    wa
    #
    @20
    @27
    @8
    @20
    @21
    simprl
    @29
    cc0
    cN
    cdvds
    wbr
    #
    @27
    @29
    cM
    cc0
    cN
    cdvds
    @8
    @20
    @21
    simprr
    @3
    @5
    @6
    @22
    simplrr
    eqbrtrrd
    @29
    @2
    @30
    @27
    wb
    @0
    @1
    @2
    @7
    @22
    simpll3
    cN
    0dvds
    syl
    mpbid
    jca
    ex
    @8
    @0
    @2
    @24
    @28
    wb
    @16
    @0
    @1
    @2
    @7
    simpl3
    #
    cK
    cN
    gcdeq0
    syl2anc
    #
    sylibrd
    mtod
    cK
    cM
    gcdn0cl
    syl21anc
    #
    nnzd
    #
    @17
    @31
    @9
    cM
    cN
    dvdstr
    syl3anc
    mp2and
    @8
    @19
    @0
    @2
    @28
    wn
    @12
    @13
    wa
    @14
    wi
    @34
    @16
    @31
    @8
    @24
    @28
    @26
    @32
    mtbid
    @9
    cK
    cN
    dvdslegcd
    syl31anc
    mp2and
    @25
    breqtrd
    @8
    @23
    @10
    @11
    wb
    @33
    @9
    nnle1eq1
    syl
    mpbid
end
