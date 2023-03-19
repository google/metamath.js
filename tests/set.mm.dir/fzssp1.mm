include "cfz.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cv.mm"
include "wcel.mm"
include "cz.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "elfzel2.mm"
include "uzid.mm"
include "peano2uz.mm"
include "fzss2.mm"
include "4syl.mm"
include "id.mm"
include "sseldd.mm"
include "ssriv.mm"

theorem fzssp1
  let cM: class M
  let cN: class N
  let vk: setvar k
  let cK: class K


  assert |- ( M ... N ) C_ ( M ... ( N + 1 ) )

  proof
    vk
    cM
    cN
    cfz
    co
    #
    cM
    cN
    c1
    caddc
    co
    #
    cfz
    co
    #
    vk
    cv
    #
    @0
    wcel
    #
    @0
    @2
    @3
    @4
    cN
    cz
    wcel
    cN
    cN
    cuz
    cfv
    #
    wcel
    @1
    @5
    wcel
    @0
    @2
    wss
    @3
    cM
    cN
    elfzel2
    cN
    uzid
    cN
    cN
    peano2uz
    cN
    cM
    @1
    fzss2
    4syl
    @4
    id
    sseldd
    ssriv
end
