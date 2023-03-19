include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cfzo.mm"
include "csn.mm"
include "cun.mm"
include "cz.mm"
include "wceq.mm"
include "eluzelz.mm"
include "fzval3.mm"
include "syl.mm"
include "fzosplitsn.mm"
include "eqtrd.mm"

theorem fzisfzounsn
  let cA: class A
  let cB: class B


  assert |- ( B e. ( ZZ>= ` A ) -> ( A ... B ) = ( ( A ..^ B ) u. { B } ) )

  proof
    cB
    cA
    cuz
    cfv
    wcel
    #
    cA
    cB
    cfz
    co
    #
    cA
    cB
    c1
    caddc
    co
    cfzo
    co
    #
    cA
    cB
    cfzo
    co
    cB
    csn
    cun
    @0
    cB
    cz
    wcel
    @1
    @2
    wceq
    cA
    cB
    eluzelz
    cA
    cB
    fzval3
    syl
    cA
    cB
    fzosplitsn
    eqtrd
end
