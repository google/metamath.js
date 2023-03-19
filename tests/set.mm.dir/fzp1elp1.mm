include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "cuz.mm"
include "cfv.mm"
include "elfzuz.mm"
include "peano2uz.mm"
include "syl.mm"
include "elfzuz3.mm"
include "eluzp1p1.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"

theorem fzp1elp1
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ... N ) -> ( K + 1 ) e. ( M ... ( N + 1 ) ) )

  proof
    cK
    cM
    cN
    cfz
    co
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
    c1
    caddc
    co
    #
    @1
    cuz
    cfv
    wcel
    #
    @1
    cM
    @4
    cfz
    co
    wcel
    @0
    cK
    @2
    wcel
    @3
    cK
    cM
    cN
    elfzuz
    cM
    cK
    peano2uz
    syl
    @0
    cN
    cK
    cuz
    cfv
    wcel
    @5
    cK
    cM
    cN
    elfzuz3
    cK
    cN
    eluzp1p1
    syl
    @1
    cM
    @4
    elfzuzb
    sylanbrc
end
