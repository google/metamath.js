include "cvv.mm"
include "wcel.mm"
include "cword.mm"
include "wrdexg.mm"
include "ax-mp.mm"

theorem wrdexi
  let cS: class S
  assume wrdexi.1: |- S e. _V


  assert |- Word S e. _V

  proof
    cS
    cvv
    wcel
    cS
    cword
    cvv
    wcel
    wrdexi.1
    cS
    cvv
    wrdexg
    ax-mp
end
