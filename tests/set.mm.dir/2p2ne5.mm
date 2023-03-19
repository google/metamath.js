include "c2.mm"
include "caddc.mm"
include "co.mm"
include "c4.mm"
include "c5.mm"
include "2p2e4.mm"
include "4re.mm"
include "4lt5.mm"
include "ltneii.mm"
include "eqnetri.mm"

theorem 2p2ne5
  let vk: setvar k
  let vx: setvar x


  assert |- ( 2 + 2 ) =/= 5

  proof
    c2
    c2
    caddc
    co
    c4
    c5
    2p2e4
    c4
    c5
    4re
    4lt5
    ltneii
    eqnetri
end
