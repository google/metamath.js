include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "caddc.mm"
include "cconcat.mm"
include "cop.mm"
include "csubstr.mm"
include "cmin.mm"
include "cfzo.mm"
include "wfn.mm"
include "ccatcl.mm"
include "adantr.mm"
include "simprl.mm"
include "wi.mm"
include "ccatlen.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "biimpcd.mm"
include "adantl.mm"
include "impcom.mm"
include "swrdvalfn.mm"
include "syl3anc.mm"

theorem swrdccatfn
  let cA: class A
  let cB: class B
  let cM: class M
  let cN: class N
  let cV: class V


  assert |- ( ( ( A e. Word V /\ B e. Word V ) /\ ( M e. ( 0 ... N ) /\ N e. ( 0 ... ( ( # ` A ) + ( # ` B ) ) ) ) ) -> ( ( A ++ B ) substr <. M , N >. ) Fn ( 0 ..^ ( N - M ) ) )

  proof
    cA
    cV
    cword
    #
    wcel
    cB
    @0
    wcel
    wa
    #
    cM
    cc0
    cN
    cfz
    co
    wcel
    #
    cN
    cc0
    cA
    chash
    cfv
    cB
    chash
    cfv
    caddc
    co
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    wa
    cA
    cB
    cconcat
    co
    #
    @0
    wcel
    #
    @2
    cN
    cc0
    @7
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    @7
    cM
    cN
    cop
    csubstr
    co
    cc0
    cN
    cM
    cmin
    co
    cfzo
    co
    wfn
    @1
    @8
    @6
    cV
    cA
    cB
    ccatcl
    adantr
    @1
    @2
    @5
    simprl
    @6
    @1
    @11
    @5
    @1
    @11
    wi
    @2
    @1
    @5
    @11
    @1
    @4
    @10
    cN
    @1
    @3
    @9
    cc0
    cfz
    @1
    @9
    @3
    cV
    cA
    cB
    ccatlen
    eqcomd
    oveq2d
    eleq2d
    biimpcd
    adantl
    impcom
    @7
    cM
    cN
    cV
    swrdvalfn
    syl3anc
end
