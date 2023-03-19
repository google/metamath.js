include "cword.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cmin.mm"
include "ccsh.mm"
include "caddc.mm"
include "cmo.mm"
include "cz.mm"
include "cc0.mm"
include "cfzo.mm"
include "wceq.mm"
include "simpl.mm"
include "elfzelz.mm"
include "adantl.mm"
include "cn.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "elfz1b.mm"
include "simp2.mm"
include "sylbi.mm"
include "fzo0end.mm"
include "syl.mm"
include "cshwidxmod.mm"
include "syl3anc.mm"
include "cc.mm"
include "nncn.mm"
include "1cnd.mm"
include "adantr.mm"
include "3jca.mm"
include "3adant3.mm"
include "subadd23.mm"
include "oveq1d.mm"
include "cn0.mm"
include "clt.mm"
include "nnm1nn0.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "wb.mm"
include "nnz.mm"
include "anim12i.mm"
include "zlem1lt.mm"
include "mpbid.mm"
include "addmodid.mm"
include "eqtrd.mm"
include "fveq2d.mm"

theorem cshwidxn
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ N e. ( 1 ... ( # ` W ) ) ) -> ( ( W cyclShift N ) ` ( ( # ` W ) - 1 ) ) = ( W ` ( N - 1 ) ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cN
    c1
    cW
    chash
    cfv
    #
    cfz
    co
    wcel
    #
    wa
    #
    @1
    c1
    cmin
    co
    #
    cW
    cN
    ccsh
    co
    cfv
    #
    @4
    cN
    caddc
    co
    #
    @1
    cmo
    co
    #
    cW
    cfv
    #
    cN
    c1
    cmin
    co
    #
    cW
    cfv
    #
    @3
    @0
    cN
    cz
    wcel
    #
    @4
    cc0
    @1
    cfzo
    co
    wcel
    #
    @5
    @8
    wceq
    @0
    @2
    simpl
    @2
    @11
    @0
    cN
    c1
    @1
    elfzelz
    adantl
    @3
    @1
    cn
    wcel
    #
    @12
    @2
    @13
    @0
    @2
    cN
    cn
    wcel
    #
    @13
    cN
    @1
    cle
    wbr
    #
    w3a
    #
    @13
    @1
    cN
    elfz1b
    #
    @14
    @13
    @15
    simp2
    #
    sylbi
    adantl
    @1
    fzo0end
    syl
    @4
    cN
    cV
    cW
    cshwidxmod
    syl3anc
    @2
    @8
    @10
    wceq
    @0
    @2
    @7
    @9
    cW
    @2
    @7
    @1
    @9
    caddc
    co
    #
    @1
    cmo
    co
    #
    @9
    @2
    @6
    @19
    @1
    cmo
    @2
    @1
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    w3a
    #
    @6
    @19
    wceq
    @2
    @16
    @24
    @17
    @14
    @13
    @24
    @15
    @14
    @13
    wa
    #
    @21
    @22
    @23
    @13
    @21
    @14
    @1
    nncn
    adantl
    @25
    1cnd
    @14
    @23
    @13
    cN
    nncn
    adantr
    3jca
    3adant3
    sylbi
    @1
    c1
    cN
    subadd23
    syl
    oveq1d
    @2
    @9
    cn0
    wcel
    #
    @13
    @9
    @1
    clt
    wbr
    #
    w3a
    #
    @20
    @9
    wceq
    @2
    @16
    @28
    @17
    @16
    @26
    @13
    @27
    @14
    @13
    @26
    @15
    cN
    nnm1nn0
    3ad2ant1
    @18
    @16
    @15
    @27
    @14
    @13
    @15
    simp3
    @16
    @11
    @1
    cz
    wcel
    #
    wa
    #
    @15
    @27
    wb
    @14
    @13
    @30
    @15
    @14
    @11
    @13
    @29
    cN
    nnz
    @1
    nnz
    anim12i
    3adant3
    cN
    @1
    zlem1lt
    syl
    mpbid
    3jca
    sylbi
    @9
    @1
    addmodid
    syl
    eqtrd
    fveq2d
    adantl
    eqtrd
end
