include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "c2.mm"
include "1red.mm"
include "2re.mm"
include "a1i.mm"
include "id.mm"
include "cle.mm"
include "wbr.mm"
include "1le2.mm"
include "leadd2dd.mm"

theorem p1lep2
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. RR -> ( N + 1 ) <_ ( N + 2 ) )

  proof
    cN
    cr
    wcel
    #
    c1
    c2
    cN
    @0
    1red
    c2
    cr
    wcel
    @0
    2re
    a1i
    @0
    id
    c1
    c2
    cle
    wbr
    @0
    1le2
    a1i
    leadd2dd
end
