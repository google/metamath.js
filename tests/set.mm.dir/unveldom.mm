include "cprb.mm"
include "wcel.mm"
include "id.mm"
include "unveldomd.mm"

theorem unveldom
  let cP: class P


  assert |- ( P e. Prob -> U. dom P e. dom P )

  proof
    cP
    cprb
    wcel
    #
    cP
    @0
    id
    unveldomd
end
