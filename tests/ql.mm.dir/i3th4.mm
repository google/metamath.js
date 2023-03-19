include "wt.mm"
include "wi3.mm"
include "i31.mm"
include "i3id.mm"
include "ax-r1.mm"
include "li3.mm"
include "rbi.mm"
include "wed.mm"

theorem i3th4
  let wva: term a
  let wvb: term b


  assert |- ( a ->3 ( b ->3 b ) ) = 1

  proof
    wva
    wt
    wi3
    #
    wt
    wva
    wvb
    wvb
    wi3
    #
    wi3
    #
    wt
    wva
    i31
    @0
    @2
    wt
    wt
    @1
    wva
    @1
    wt
    wvb
    i3id
    ax-r1
    li3
    rbi
    wed
end
