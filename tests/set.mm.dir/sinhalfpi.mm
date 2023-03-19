include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "csin.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "ccos.mm"
include "cc0.mm"
include "sinhalfpilem.mm"
include "simpli.mm"

theorem sinhalfpi



  assert |- ( sin ` ( _pi / 2 ) ) = 1

  proof
    cpi
    c2
    cdiv
    co
    #
    csin
    cfv
    c1
    wceq
    @0
    ccos
    cfv
    cc0
    wceq
    sinhalfpilem
    simpli
end
