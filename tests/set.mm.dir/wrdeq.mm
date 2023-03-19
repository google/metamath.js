include "wss.mm"
include "wa.mm"
include "cword.mm"
include "wceq.mm"
include "sswrd.mm"
include "anim12i.mm"
include "eqss.mm"
include "3imtr4i.mm"

theorem wrdeq
  let cS: class S
  let cT: class T


  assert |- ( S = T -> Word S = Word T )

  proof
    cS
    cT
    wss
    #
    cT
    cS
    wss
    #
    wa
    cS
    cword
    #
    cT
    cword
    #
    wss
    #
    @3
    @2
    wss
    #
    wa
    cS
    cT
    wceq
    @2
    @3
    wceq
    @0
    @4
    @1
    @5
    cS
    cT
    sswrd
    cT
    cS
    sswrd
    anim12i
    cS
    cT
    eqss
    @2
    @3
    eqss
    3imtr4i
end
