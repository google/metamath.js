include "cword.mm"
include "wcel.mm"
include "wf.mm"
include "wa.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "ccom.mm"
include "simpr.mm"
include "wrdf.mm"
include "adantr.mm"
include "fco.mm"
include "syl2anc.mm"
include "iswrdi.mm"
include "syl.mm"

theorem wrdco
  let cA: class A
  let cB: class B
  let cF: class F
  let cW: class W


  assert |- ( ( W e. Word A /\ F : A --> B ) -> ( F o. W ) e. Word B )

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
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    cB
    cF
    cW
    ccom
    #
    wf
    #
    @5
    cB
    cword
    wcel
    @2
    @1
    @4
    cA
    cW
    wf
    #
    @6
    @0
    @1
    simpr
    @0
    @7
    @1
    cA
    cW
    wrdf
    adantr
    @4
    cA
    cB
    cF
    cW
    fco
    syl2anc
    cB
    @3
    @5
    iswrdi
    syl
end
