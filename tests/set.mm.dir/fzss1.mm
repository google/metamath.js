include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "wa.mm"
include "elfzuz.mm"
include "id.mm"
include "uztrn.mm"
include "syl2anr.mm"
include "elfzuz3.mm"
include "adantl.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "ex.mm"
include "ssrdv.mm"

theorem fzss1
  let cK: class K
  let cM: class M
  let cN: class N
  let vk: setvar k


  assert |- ( K e. ( ZZ>= ` M ) -> ( K ... N ) C_ ( M ... N ) )

  proof
    cK
    cM
    cuz
    cfv
    #
    wcel
    #
    vk
    cK
    cN
    cfz
    co
    #
    cM
    cN
    cfz
    co
    #
    @1
    vk
    cv
    #
    @2
    wcel
    #
    @4
    @3
    wcel
    #
    @1
    @5
    wa
    @4
    @0
    wcel
    #
    cN
    @4
    cuz
    cfv
    wcel
    #
    @6
    @5
    @4
    cK
    cuz
    cfv
    wcel
    @1
    @7
    @1
    @4
    cK
    cN
    elfzuz
    @1
    id
    cK
    @4
    cM
    uztrn
    syl2anr
    @5
    @8
    @1
    @4
    cK
    cN
    elfzuz3
    adantl
    @4
    cM
    cN
    elfzuzb
    sylanbrc
    ex
    ssrdv
end
