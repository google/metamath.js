include "wceq.mm"
include "cword.mm"
include "wrdeq.mm"
include "ax-mp.mm"

theorem wrdeqi
  let cS: class S
  let cT: class T
  assume wrdeqi.1: |- S = T


  assert |- Word S = Word T

  proof
    cS
    cT
    wceq
    cS
    cword
    cT
    cword
    wceq
    wrdeqi.1
    cS
    cT
    wrdeq
    ax-mp
end
