include "cword.mm"
include "wcel.mm"
include "cn0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "w3a.mm"
include "cs2.mm"
include "cop.mm"
include "csubstr.mm"
include "c2.mm"
include "cconcat.mm"
include "cs1.mm"
include "wceq.mm"
include "simp1.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "simp2.mm"
include "elfzo0.mm"
include "simp2bi.mm"
include "3ad2ant3.mm"
include "nn0red.mm"
include "peano2nn0.mm"
include "syl.mm"
include "nnred.mm"
include "lep1d.mm"
include "elfzolt2.mm"
include "lelttrd.mm"
include "syl3anbrc.mm"
include "swrds1.mm"
include "syl2anc.mm"
include "cc.mm"
include "nn0cn.mm"
include "3ad2ant2.mm"
include "ax-1cn.mm"
include "addass.mm"
include "mp3an23.mm"
include "df-2.mm"
include "oveq2i.mm"
include "syl6reqr.mm"
include "opeq2d.mm"
include "oveq2d.mm"
include "3adant2.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "df-s2.mm"
include "cfz.mm"
include "cle.mm"
include "elfz2nn0.mm"
include "eqeltrd.mm"
include "breqtrrd.mm"
include "fzofzp1.mm"
include "ccatswrd.mm"
include "syl13anc.mm"
include "eqtr2d.mm"

theorem swrds2
  let cA: class A
  let cI: class I
  let cW: class W


  assert |- ( ( W e. Word A /\ I e. NN0 /\ ( I + 1 ) e. ( 0 ..^ ( # ` W ) ) ) -> ( W substr <. I , ( I + 2 ) >. ) = <" ( W ` I ) ( W ` ( I + 1 ) ) "> )

  proof
    cW
    cA
    cword
    wcel
    #
    cI
    cn0
    wcel
    #
    cI
    c1
    caddc
    co
    #
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    wcel
    #
    w3a
    #
    cI
    cW
    cfv
    #
    @2
    cW
    cfv
    #
    cs2
    #
    cW
    cI
    @2
    cop
    csubstr
    co
    #
    cW
    @2
    cI
    c2
    caddc
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
    cW
    cI
    @11
    cop
    csubstr
    co
    #
    @6
    @14
    @7
    cs1
    #
    @8
    cs1
    #
    cconcat
    co
    @9
    @6
    @10
    @16
    @13
    @17
    cconcat
    @6
    @0
    cI
    @4
    wcel
    #
    @10
    @16
    wceq
    @0
    @1
    @5
    simp1
    #
    @6
    @1
    @3
    cn
    wcel
    #
    cI
    @3
    clt
    wbr
    @18
    @0
    @1
    @5
    simp2
    #
    @5
    @0
    @20
    @1
    @5
    @2
    cn0
    wcel
    #
    @20
    @2
    @3
    clt
    wbr
    #
    @2
    @3
    elfzo0
    simp2bi
    3ad2ant3
    #
    @6
    cI
    @2
    @3
    @6
    cI
    @21
    nn0red
    #
    @6
    @2
    @6
    @1
    @22
    @21
    cI
    peano2nn0
    syl
    #
    nn0red
    #
    @6
    @3
    @24
    nnred
    @6
    cI
    @25
    lep1d
    #
    @5
    @0
    @23
    @1
    @2
    cc0
    @3
    elfzolt2
    3ad2ant3
    lelttrd
    cI
    @3
    elfzo0
    syl3anbrc
    cA
    cI
    cW
    swrds1
    syl2anc
    @6
    @13
    cW
    @2
    @2
    c1
    caddc
    co
    #
    cop
    #
    csubstr
    co
    #
    @17
    @6
    @12
    @30
    cW
    csubstr
    @6
    @11
    @29
    @2
    @6
    cI
    cc
    wcel
    #
    @11
    @29
    wceq
    @1
    @0
    @32
    @5
    cI
    nn0cn
    3ad2ant2
    @32
    @29
    cI
    c1
    c1
    caddc
    co
    #
    caddc
    co
    #
    @11
    @32
    c1
    cc
    wcel
    #
    @35
    @29
    @34
    wceq
    ax-1cn
    ax-1cn
    cI
    c1
    c1
    addass
    mp3an23
    c2
    @33
    cI
    caddc
    df-2
    oveq2i
    syl6reqr
    syl
    #
    opeq2d
    oveq2d
    @0
    @5
    @31
    @17
    wceq
    @1
    cA
    @2
    cW
    swrds1
    3adant2
    eqtrd
    oveq12d
    @7
    @8
    df-s2
    syl6reqr
    @6
    @0
    cI
    cc0
    @2
    cfz
    co
    wcel
    #
    @2
    cc0
    @11
    cfz
    co
    wcel
    #
    @11
    cc0
    @3
    cfz
    co
    #
    wcel
    @14
    @15
    wceq
    @19
    @6
    @1
    @22
    cI
    @2
    cle
    wbr
    @37
    @21
    @26
    @28
    cI
    @2
    elfz2nn0
    syl3anbrc
    @6
    @22
    @11
    cn0
    wcel
    @2
    @11
    cle
    wbr
    @38
    @26
    @6
    @11
    @29
    cn0
    @36
    @6
    @22
    @29
    cn0
    wcel
    @26
    @2
    peano2nn0
    syl
    eqeltrd
    @6
    @2
    @29
    @11
    cle
    @6
    @2
    @27
    lep1d
    @36
    breqtrrd
    @2
    @11
    elfz2nn0
    syl3anbrc
    @6
    @11
    @29
    @39
    @36
    @5
    @0
    @29
    @39
    wcel
    @1
    cc0
    @3
    @2
    fzofzp1
    3ad2ant3
    eqeltrd
    cA
    cW
    cI
    @2
    @11
    ccatswrd
    syl13anc
    eqtr2d
end
