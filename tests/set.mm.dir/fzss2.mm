include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "wa.mm"
include "elfzuz.mm"
include "adantl.mm"
include "elfzuz3.mm"
include "uztrn.mm"
include "sylan2.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "ex.mm"
include "ssrdv.mm"

theorem fzss2
  let cK: class K
  let cM: class M
  let cN: class N
  let vk: setvar k


  assert |- ( N e. ( ZZ>= ` K ) -> ( M ... K ) C_ ( M ... N ) )

  proof
    cN
    cK
    cuz
    cfv
    wcel
    #
    vk
    cM
    cK
    cfz
    co
    #
    cM
    cN
    cfz
    co
    #
    @0
    vk
    cv
    #
    @1
    wcel
    #
    @3
    @2
    wcel
    #
    @0
    @4
    wa
    @3
    cM
    cuz
    cfv
    wcel
    #
    cN
    @3
    cuz
    cfv
    #
    wcel
    #
    @5
    @4
    @6
    @0
    @3
    cM
    cK
    elfzuz
    adantl
    @4
    @0
    cK
    @7
    wcel
    @8
    @3
    cM
    cK
    elfzuz3
    cK
    cN
    @3
    uztrn
    sylan2
    @3
    cM
    cN
    elfzuzb
    sylanbrc
    ex
    ssrdv
end
