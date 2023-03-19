include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "cun.mm"
include "csn.mm"
include "cfz.mm"
include "wceq.mm"
include "id.mm"
include "cz.mm"
include "eluzelz.mm"
include "uzid.mm"
include "peano2uz.mm"
include "3syl.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "fzosplit.mm"
include "syl.mm"
include "fzosn.mm"
include "uneq2d.mm"
include "eqtrd.mm"

theorem fzosplitsn
  let cA: class A
  let cB: class B


  assert |- ( B e. ( ZZ>= ` A ) -> ( A ..^ ( B + 1 ) ) = ( ( A ..^ B ) u. { B } ) )

  proof
    cB
    cA
    cuz
    cfv
    wcel
    #
    cA
    cB
    c1
    caddc
    co
    #
    cfzo
    co
    #
    cA
    cB
    cfzo
    co
    #
    cB
    @1
    cfzo
    co
    #
    cun
    #
    @3
    cB
    csn
    #
    cun
    @0
    cB
    cA
    @1
    cfz
    co
    wcel
    #
    @2
    @5
    wceq
    @0
    @0
    @1
    cB
    cuz
    cfv
    #
    wcel
    #
    @7
    @0
    id
    @0
    cB
    cz
    wcel
    #
    cB
    @8
    wcel
    @9
    cA
    cB
    eluzelz
    #
    cB
    uzid
    cB
    cB
    peano2uz
    3syl
    cB
    cA
    @1
    elfzuzb
    sylanbrc
    cA
    @1
    cB
    fzosplit
    syl
    @0
    @4
    @6
    @3
    @0
    @10
    @4
    @6
    wceq
    @11
    cB
    fzosn
    syl
    uneq2d
    eqtrd
end
