include "cz.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cfzo.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cun.mm"
include "csn.mm"
include "cfz.mm"
include "wceq.mm"
include "fzolb.mm"
include "fzofzp1.mm"
include "sylbir.mm"
include "fzosplit.mm"
include "syl.mm"
include "fzosn.mm"
include "3ad2ant1.mm"
include "uneq1d.mm"
include "eqtrd.mm"

theorem fzopred
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( M e. ZZ /\ N e. ZZ /\ M < N ) -> ( M ..^ N ) = ( { M } u. ( ( M + 1 ) ..^ N ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cM
    cN
    clt
    wbr
    #
    w3a
    #
    cM
    cN
    cfzo
    co
    #
    cM
    cM
    c1
    caddc
    co
    #
    cfzo
    co
    #
    @5
    cN
    cfzo
    co
    #
    cun
    #
    cM
    csn
    #
    @7
    cun
    @3
    @5
    cM
    cN
    cfz
    co
    wcel
    #
    @4
    @8
    wceq
    @3
    cM
    @4
    wcel
    @10
    cM
    cN
    fzolb
    cM
    cN
    cM
    fzofzp1
    sylbir
    cM
    cN
    @5
    fzosplit
    syl
    @3
    @6
    @9
    @7
    @0
    @1
    @6
    @9
    wceq
    @2
    cM
    fzosn
    3ad2ant1
    uneq1d
    eqtrd
end
