include "cword.mm"
include "wcel.mm"
include "wf.mm"
include "wa.mm"
include "ccom.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wfn.mm"
include "wceq.mm"
include "simpr.mm"
include "wrdf.mm"
include "adantr.mm"
include "fco.mm"
include "syl2anc.mm"
include "ffn.mm"
include "hashfn.mm"
include "3syl.mm"
include "eqtr4d.mm"

theorem lenco
  let cA: class A
  let cB: class B
  let cF: class F
  let cW: class W


  assert |- ( ( W e. Word A /\ F : A --> B ) -> ( # ` ( F o. W ) ) = ( # ` W ) )

  proof
    cW
    cA
    cword
    wcel
    #
    cA
    cB
    cF
    wf
    #
    wa
    #
    cF
    cW
    ccom
    #
    chash
    cfv
    #
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    chash
    cfv
    #
    @5
    @2
    @6
    cB
    @3
    wf
    #
    @3
    @6
    wfn
    @4
    @7
    wceq
    @2
    @1
    @6
    cA
    cW
    wf
    #
    @8
    @0
    @1
    simpr
    @0
    @9
    @1
    cA
    cW
    wrdf
    adantr
    #
    @6
    cA
    cB
    cF
    cW
    fco
    syl2anc
    @6
    cB
    @3
    ffn
    @6
    @3
    hashfn
    3syl
    @2
    @9
    cW
    @6
    wfn
    @5
    @7
    wceq
    @10
    @6
    cA
    cW
    ffn
    @6
    cW
    hashfn
    3syl
    eqtr4d
end
