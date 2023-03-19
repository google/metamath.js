include "cz.mm"
include "wcel.mm"
include "cprime.mm"
include "cn0.mm"
include "cr.mm"
include "cneg.mm"
include "cn.mm"
include "wa.mm"
include "wo.mm"
include "cexp.mm"
include "co.mm"
include "cpc.mm"
include "wceq.mm"
include "elznn0nn.mm"
include "pcidlem.mm"
include "c1.mm"
include "cdiv.mm"
include "cc.mm"
include "prmnn.mm"
include "adantr.mm"
include "nncnd.mm"
include "simprl.mm"
include "recnd.mm"
include "nnnn0.mm"
include "ad2antll.mm"
include "expneg2.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "cmin.mm"
include "cc0.mm"
include "wne.mm"
include "simpl.mm"
include "1zzd.mm"
include "ax-1ne0.mm"
include "a1i.mm"
include "nnexpcld.mm"
include "pcdiv.mm"
include "syl121anc.mm"
include "pc1.mm"
include "syldan.mm"
include "oveq12d.mm"
include "df-neg.mm"
include "negnegd.mm"
include "syl5eqr.mm"
include "eqtrd.mm"
include "jaodan.mm"
include "sylan2b.mm"

theorem pcid
  let cA: class A
  let cP: class P


  assert |- ( ( P e. Prime /\ A e. ZZ ) -> ( P pCnt ( P ^ A ) ) = A )

  proof
    cA
    cz
    wcel
    cP
    cprime
    wcel
    #
    cA
    cn0
    wcel
    #
    cA
    cr
    wcel
    #
    cA
    cneg
    #
    cn
    wcel
    #
    wa
    #
    wo
    cP
    cP
    cA
    cexp
    co
    #
    cpc
    co
    #
    cA
    wceq
    #
    cA
    elznn0nn
    @0
    @1
    @8
    @5
    cA
    cP
    pcidlem
    @0
    @5
    wa
    #
    @7
    cP
    c1
    cP
    @3
    cexp
    co
    #
    cdiv
    co
    #
    cpc
    co
    #
    cA
    @9
    @6
    @11
    cP
    cpc
    @9
    cP
    cc
    wcel
    cA
    cc
    wcel
    @3
    cn0
    wcel
    #
    @6
    @11
    wceq
    @9
    cP
    @0
    cP
    cn
    wcel
    @5
    cP
    prmnn
    adantr
    #
    nncnd
    @9
    cA
    @0
    @2
    @4
    simprl
    recnd
    #
    @4
    @13
    @0
    @2
    @3
    nnnn0
    ad2antll
    #
    cP
    cA
    expneg2
    syl3anc
    oveq2d
    @9
    @12
    cP
    c1
    cpc
    co
    #
    cP
    @10
    cpc
    co
    #
    cmin
    co
    #
    cA
    @9
    @0
    c1
    cz
    wcel
    c1
    cc0
    wne
    #
    @10
    cn
    wcel
    @12
    @19
    wceq
    @0
    @5
    simpl
    @9
    1zzd
    @20
    @9
    ax-1ne0
    a1i
    @9
    cP
    @3
    @14
    @16
    nnexpcld
    c1
    @10
    cP
    pcdiv
    syl121anc
    @9
    @19
    cc0
    @3
    cmin
    co
    #
    cA
    @9
    @17
    cc0
    @18
    @3
    cmin
    @0
    @17
    cc0
    wceq
    @5
    cP
    pc1
    adantr
    @0
    @5
    @13
    @18
    @3
    wceq
    @16
    @3
    cP
    pcidlem
    syldan
    oveq12d
    @9
    @21
    @3
    cneg
    cA
    @3
    df-neg
    @9
    cA
    @15
    negnegd
    syl5eqr
    eqtrd
    eqtrd
    eqtrd
    jaodan
    sylan2b
end
