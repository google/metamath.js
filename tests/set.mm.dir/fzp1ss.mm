include "cz.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "wss.mm"
include "uzid.mm"
include "peano2uz.mm"
include "fzss1.mm"
include "3syl.mm"

theorem fzp1ss
  let cM: class M
  let cN: class N


  assert |- ( M e. ZZ -> ( ( M + 1 ) ... N ) C_ ( M ... N ) )

  proof
    cM
    cz
    wcel
    cM
    cM
    cuz
    cfv
    #
    wcel
    cM
    c1
    caddc
    co
    #
    @0
    wcel
    @1
    cN
    cfz
    co
    cM
    cN
    cfz
    co
    wss
    cM
    uzid
    cM
    cM
    peano2uz
    @1
    cM
    cN
    fzss1
    3syl
end
