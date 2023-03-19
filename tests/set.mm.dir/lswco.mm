include "cword.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wf.mm"
include "w3a.mm"
include "ccom.mm"
include "clsw.mm"
include "cfv.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "wfun.mm"
include "wa.mm"
include "cvv.mm"
include "wceq.mm"
include "ffun.mm"
include "anim1i.mm"
include "ancoms.mm"
include "3adant2.mm"
include "cofunexg.mm"
include "lsw.mm"
include "3syl.mm"
include "lenco.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "cc0.mm"
include "cfzo.mm"
include "wrdf.mm"
include "adantr.mm"
include "cn.mm"
include "lennncl.mm"
include "fzo0end.mm"
include "syl.mm"
include "jca.mm"
include "3adant3.mm"
include "fvco3.mm"
include "3ad2ant1.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem lswco
  let cA: class A
  let cB: class B
  let cF: class F
  let cW: class W


  assert |- ( ( W e. Word A /\ W =/= (/) /\ F : A --> B ) -> ( lastS ` ( F o. W ) ) = ( F ` ( lastS ` W ) ) )

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
    cA
    cB
    cF
    wf
    #
    w3a
    #
    cF
    cW
    ccom
    #
    clsw
    cfv
    #
    @5
    chash
    cfv
    #
    c1
    cmin
    co
    #
    @5
    cfv
    #
    cW
    chash
    cfv
    #
    c1
    cmin
    co
    #
    @5
    cfv
    #
    cW
    clsw
    cfv
    #
    cF
    cfv
    #
    @4
    cF
    wfun
    #
    @1
    wa
    #
    @5
    cvv
    wcel
    @6
    @9
    wceq
    @1
    @3
    @16
    @2
    @3
    @1
    @16
    @3
    @15
    @1
    cA
    cB
    cF
    ffun
    anim1i
    ancoms
    3adant2
    cF
    cW
    @0
    cofunexg
    @5
    cvv
    lsw
    3syl
    @4
    @8
    @11
    @5
    @4
    @7
    @10
    c1
    cmin
    @1
    @3
    @7
    @10
    wceq
    @2
    cA
    cB
    cF
    cW
    lenco
    3adant2
    oveq1d
    fveq2d
    @4
    @12
    @11
    cW
    cfv
    #
    cF
    cfv
    #
    @14
    @4
    cc0
    @10
    cfzo
    co
    #
    cA
    cW
    wf
    #
    @11
    @19
    wcel
    #
    wa
    #
    @12
    @18
    wceq
    @1
    @2
    @22
    @3
    @1
    @2
    wa
    #
    @20
    @21
    @1
    @20
    @2
    cA
    cW
    wrdf
    adantr
    @23
    @10
    cn
    wcel
    @21
    cA
    cW
    lennncl
    @10
    fzo0end
    syl
    jca
    3adant3
    @19
    cA
    @11
    cF
    cW
    fvco3
    syl
    @4
    @17
    @13
    cF
    @4
    @13
    @17
    @1
    @2
    @13
    @17
    wceq
    @3
    cW
    @0
    lsw
    3ad2ant1
    eqcomd
    fveq2d
    eqtrd
    3eqtrd
end
