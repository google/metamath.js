include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "cuz.mm"
include "cfv.mm"
include "cun.mm"
include "wceq.mm"
include "elfzuz.mm"
include "peano2uz.mm"
include "syl.mm"
include "elfzuz3.mm"
include "fzsplit2.mm"
include "syl2anc.mm"

theorem fzsplit
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( K e. ( M ... N ) -> ( M ... N ) = ( ( M ... K ) u. ( ( K + 1 ) ... N ) ) )

  proof
    cK
    cM
    cN
    cfz
    co
    #
    wcel
    #
    cK
    c1
    caddc
    co
    #
    cM
    cuz
    cfv
    #
    wcel
    #
    cN
    cK
    cuz
    cfv
    wcel
    @0
    cM
    cK
    cfz
    co
    @2
    cN
    cfz
    co
    cun
    wceq
    @1
    cK
    @3
    wcel
    @4
    cK
    cM
    cN
    elfzuz
    cM
    cK
    peano2uz
    syl
    cK
    cM
    cN
    elfzuz3
    cK
    cM
    cN
    fzsplit2
    syl2anc
end
