include "cword.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cc0.mm"
include "c1.mm"
include "cop.mm"
include "csubstr.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cconcat.mm"
include "cs1.mm"
include "cfz.mm"
include "wceq.mm"
include "simpl.mm"
include "cn0.mm"
include "1nn0.mm"
include "0elfz.mm"
include "mp1i.mm"
include "cfn.mm"
include "wrdfin.mm"
include "1elfz0hash.mm"
include "sylan.mm"
include "lennncl.mm"
include "nnnn0d.mm"
include "cuz.mm"
include "eluzfz2.mm"
include "nn0uz.mm"
include "eleq2s.mm"
include "syl.mm"
include "ccatswrd.mm"
include "syl13anc.mm"
include "caddc.mm"
include "0p1e1.mm"
include "opeq2i.mm"
include "oveq2i.mm"
include "cfzo.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "0nn0.mm"
include "a1i.mm"
include "hashgt0.mm"
include "elfzo0.mm"
include "syl3anbrc.mm"
include "swrds1.mm"
include "syldan.mm"
include "syl5eqr.mm"
include "oveq1d.mm"
include "swrdid.mm"
include "adantr.mm"
include "3eqtr3rd.mm"

theorem wrdeqs1cat
  let cA: class A
  let cW: class W


  assert |- ( ( W e. Word A /\ W =/= (/) ) -> W = ( <" ( W ` 0 ) "> ++ ( W substr <. 1 , ( # ` W ) >. ) ) )

  proof
    cW
    cA
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
    c1
    cop
    #
    csubstr
    co
    #
    cW
    c1
    cW
    chash
    cfv
    #
    cop
    csubstr
    co
    #
    cconcat
    co
    #
    cW
    cc0
    @6
    cop
    csubstr
    co
    #
    cc0
    cW
    cfv
    cs1
    #
    @7
    cconcat
    co
    cW
    @3
    @1
    cc0
    cc0
    c1
    cfz
    co
    wcel
    #
    c1
    cc0
    @6
    cfz
    co
    #
    wcel
    #
    @6
    @12
    wcel
    #
    @8
    @9
    wceq
    @1
    @2
    simpl
    c1
    cn0
    wcel
    @11
    @3
    1nn0
    c1
    0elfz
    mp1i
    @1
    cW
    cfn
    wcel
    @2
    @13
    cA
    cW
    wrdfin
    cW
    1elfz0hash
    sylan
    @3
    @6
    cn0
    wcel
    @14
    @3
    @6
    cA
    cW
    lennncl
    #
    nnnn0d
    @14
    @6
    cc0
    cuz
    cfv
    cn0
    cc0
    @6
    eluzfz2
    nn0uz
    eleq2s
    syl
    cA
    cW
    cc0
    c1
    @6
    ccatswrd
    syl13anc
    @3
    @5
    @10
    @7
    cconcat
    @3
    @5
    cW
    cc0
    cc0
    c1
    caddc
    co
    #
    cop
    #
    csubstr
    co
    #
    @10
    @17
    @4
    cW
    csubstr
    @16
    c1
    cc0
    0p1e1
    opeq2i
    oveq2i
    @1
    @2
    cc0
    cc0
    @6
    cfzo
    co
    wcel
    #
    @18
    @10
    wceq
    @3
    cc0
    cn0
    wcel
    #
    @6
    cn
    wcel
    cc0
    @6
    clt
    wbr
    @19
    @20
    @3
    0nn0
    a1i
    @15
    cW
    @0
    hashgt0
    cc0
    @6
    elfzo0
    syl3anbrc
    cA
    cc0
    cW
    swrds1
    syldan
    syl5eqr
    oveq1d
    @1
    @9
    cW
    wceq
    @2
    cA
    cW
    swrdid
    adantr
    3eqtr3rd
end
