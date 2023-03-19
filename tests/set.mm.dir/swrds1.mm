include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "cop.mm"
include "csubstr.mm"
include "cs1.mm"
include "wceq.mm"
include "swrdcl.mm"
include "adantr.mm"
include "cmin.mm"
include "cfz.mm"
include "simpl.mm"
include "cuz.mm"
include "elfzouz.mm"
include "adantl.mm"
include "cz.mm"
include "elfzoelz.mm"
include "uzid.mm"
include "peano2uz.mm"
include "3syl.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "fzofzp1.mm"
include "swrdlen.mm"
include "syl3anc.mm"
include "cc.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "pncan2.mm"
include "sylancl.mm"
include "eqtrd.mm"
include "eqs1.mm"
include "syl2anc.mm"
include "csn.mm"
include "0z.mm"
include "snidg.mm"
include "ax-mp.mm"
include "oveq2d.mm"
include "fzo01.mm"
include "syl6eq.mm"
include "syl5eleqr.mm"
include "swrdfv.mm"
include "syl31anc.mm"
include "addid2.mm"
include "eqcomd.mm"
include "syl.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "s1eqd.mm"

theorem swrds1
  let cA: class A
  let cI: class I
  let cW: class W


  assert |- ( ( W e. Word A /\ I e. ( 0 ..^ ( # ` W ) ) ) -> ( W substr <. I , ( I + 1 ) >. ) = <" ( W ` I ) "> )

  proof
    cW
    cA
    cword
    #
    wcel
    #
    cI
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    wcel
    #
    wa
    #
    cW
    cI
    cI
    c1
    caddc
    co
    #
    cop
    csubstr
    co
    #
    cc0
    @6
    cfv
    #
    cs1
    #
    cI
    cW
    cfv
    #
    cs1
    @4
    @6
    @0
    wcel
    #
    @6
    chash
    cfv
    #
    c1
    wceq
    @6
    @8
    wceq
    @1
    @10
    @3
    cA
    cW
    cI
    @5
    swrdcl
    adantr
    @4
    @11
    @5
    cI
    cmin
    co
    #
    c1
    @4
    @1
    cI
    cc0
    @5
    cfz
    co
    wcel
    #
    @5
    cc0
    @2
    cfz
    co
    wcel
    #
    @11
    @12
    wceq
    @1
    @3
    simpl
    #
    @4
    cI
    cc0
    cuz
    cfv
    wcel
    #
    @5
    cI
    cuz
    cfv
    #
    wcel
    #
    @13
    @3
    @16
    @1
    cI
    cc0
    @2
    elfzouz
    adantl
    @4
    cI
    cz
    wcel
    #
    cI
    @17
    wcel
    @18
    @3
    @19
    @1
    cI
    cc0
    @2
    elfzoelz
    adantl
    #
    cI
    uzid
    cI
    cI
    peano2uz
    3syl
    cI
    cc0
    @5
    elfzuzb
    sylanbrc
    #
    @3
    @14
    @1
    cc0
    @2
    cI
    fzofzp1
    adantl
    #
    cA
    cW
    cI
    @5
    swrdlen
    syl3anc
    @4
    cI
    cc
    wcel
    #
    c1
    cc
    wcel
    @12
    c1
    wceq
    @4
    cI
    @20
    zcnd
    #
    ax-1cn
    cI
    c1
    pncan2
    sylancl
    #
    eqtrd
    cA
    @6
    eqs1
    syl2anc
    @4
    @7
    @9
    @4
    @7
    cc0
    cI
    caddc
    co
    #
    cW
    cfv
    #
    @9
    @4
    @1
    @13
    @14
    cc0
    cc0
    @12
    cfzo
    co
    #
    wcel
    @7
    @27
    wceq
    @15
    @21
    @22
    @4
    cc0
    cc0
    csn
    #
    @28
    cc0
    cz
    wcel
    cc0
    @29
    wcel
    0z
    cc0
    cz
    snidg
    ax-mp
    @4
    @28
    cc0
    c1
    cfzo
    co
    @29
    @4
    @12
    c1
    cc0
    cfzo
    @25
    oveq2d
    fzo01
    syl6eq
    syl5eleqr
    cA
    cW
    cI
    @5
    cc0
    swrdfv
    syl31anc
    @4
    cI
    @26
    cW
    @4
    @23
    cI
    @26
    wceq
    @24
    @23
    @26
    cI
    cI
    addid2
    eqcomd
    syl
    fveq2d
    eqtr4d
    s1eqd
    eqtrd
end
