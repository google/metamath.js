include "cword.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cop.mm"
include "csubstr.mm"
include "clsw.mm"
include "cs1.mm"
include "cconcat.mm"
include "caddc.mm"
include "cfzo.mm"
include "wceq.mm"
include "cn.mm"
include "lennncl.mm"
include "fzo0end.mm"
include "syl.mm"
include "swrds1.mm"
include "syldan.mm"
include "nncn.mm"
include "1cnd.mm"
include "npcand.mm"
include "eqcomd.mm"
include "opeq2d.mm"
include "oveq2d.mm"
include "lsw.mm"
include "adantr.mm"
include "s1eqd.mm"
include "3eqtr4rd.mm"
include "cfz.mm"
include "w3a.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "0elfz.mm"
include "cle.mm"
include "wbr.mm"
include "1nn0.mm"
include "a1i.mm"
include "nnnn0.mm"
include "nnge1.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "elfz1end.mm"
include "biimpi.mm"
include "fz0fzdiffz0.mm"
include "syl2anc.mm"
include "nn0fz0.mm"
include "3jca.mm"
include "ccatswrd.mm"
include "swrdid.mm"
include "3eqtrd.mm"

theorem swrdccatwrd
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ W =/= (/) ) -> ( ( W substr <. 0 , ( ( # ` W ) - 1 ) >. ) ++ <" ( lastS ` W ) "> ) = W )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cW
    c0
    wne
    #
    wa
    #
    cW
    cc0
    cW
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cop
    csubstr
    co
    #
    cW
    clsw
    cfv
    #
    cs1
    #
    cconcat
    co
    @6
    cW
    @5
    @4
    cop
    #
    csubstr
    co
    #
    cconcat
    co
    #
    cW
    cc0
    @4
    cop
    csubstr
    co
    #
    cW
    @3
    @8
    @10
    @6
    cconcat
    @3
    cW
    @5
    @5
    c1
    caddc
    co
    #
    cop
    #
    csubstr
    co
    #
    @5
    cW
    cfv
    #
    cs1
    #
    @10
    @8
    @1
    @2
    @5
    cc0
    @4
    cfzo
    co
    wcel
    #
    @15
    @17
    wceq
    @3
    @4
    cn
    wcel
    #
    @18
    cV
    cW
    lennncl
    #
    @4
    fzo0end
    syl
    cV
    @5
    cW
    swrds1
    syldan
    @3
    @9
    @14
    cW
    csubstr
    @3
    @4
    @13
    @5
    @3
    @19
    @4
    @13
    wceq
    @20
    @19
    @13
    @4
    @19
    @4
    c1
    @4
    nncn
    @19
    1cnd
    npcand
    eqcomd
    syl
    opeq2d
    oveq2d
    @3
    @7
    @16
    @1
    @7
    @16
    wceq
    @2
    cW
    @0
    lsw
    adantr
    s1eqd
    3eqtr4rd
    oveq2d
    @1
    @2
    cc0
    cc0
    @5
    cfz
    co
    wcel
    #
    @5
    cc0
    @4
    cfz
    co
    #
    wcel
    #
    @4
    @22
    wcel
    #
    w3a
    #
    @11
    @12
    wceq
    @3
    @19
    @25
    @20
    @19
    @21
    @23
    @24
    @19
    @5
    cn0
    wcel
    @21
    @4
    nnm1nn0
    @5
    0elfz
    syl
    @19
    c1
    @22
    wcel
    #
    @4
    c1
    @4
    cfz
    co
    wcel
    #
    @23
    @19
    c1
    cn0
    wcel
    #
    @4
    cn0
    wcel
    #
    c1
    @4
    cle
    wbr
    @26
    @28
    @19
    1nn0
    a1i
    @4
    nnnn0
    #
    @4
    nnge1
    c1
    @4
    elfz2nn0
    syl3anbrc
    @19
    @27
    @4
    elfz1end
    biimpi
    @4
    c1
    @4
    fz0fzdiffz0
    syl2anc
    @19
    @29
    @24
    @30
    @29
    @24
    @4
    nn0fz0
    biimpi
    syl
    3jca
    syl
    cV
    cW
    cc0
    @5
    @4
    ccatswrd
    syldan
    @1
    @12
    cW
    wceq
    @2
    cV
    cW
    swrdid
    adantr
    3eqtrd
end
