include "c3.mm"
include "c2.mm"
include "caddc.mm"
include "co.mm"
include "c4.mm"
include "c5.mm"
include "c9.mm"
include "3p2e5.mm"
include "oveq1i.mm"
include "5p4e9.mm"
include "eqtri.mm"

theorem problem1



  assert |- ( ( 3 + 2 ) + 4 ) = 9

  proof
    c3
    c2
    caddc
    co
    #
    c4
    caddc
    co
    c5
    c4
    caddc
    co
    c9
    @0
    c5
    c4
    caddc
    3p2e5
    oveq1i
    5p4e9
    eqtri
end
