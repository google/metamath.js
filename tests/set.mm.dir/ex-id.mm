include "c5.mm"
include "cid.mm"
include "wbr.mm"
include "c4.mm"
include "wn.mm"
include "wceq.mm"
include "eqid.mm"
include "cr.mm"
include "5re.mm"
include "elexi.mm"
include "ideq.mm"
include "mpbir.mm"
include "4re.mm"
include "4lt5.mm"
include "ltneii.mm"
include "nemtbir.mm"
include "pm3.2i.mm"

theorem ex-id



  assert |- ( 5 _I 5 /\ -. 4 _I 5 )

  proof
    c5
    c5
    cid
    wbr
    #
    c4
    c5
    cid
    wbr
    #
    wn
    @0
    c5
    c5
    wceq
    c5
    eqid
    c5
    c5
    c5
    cr
    5re
    elexi
    #
    ideq
    mpbir
    @1
    c4
    c5
    c4
    c5
    4re
    4lt5
    ltneii
    c4
    c5
    @2
    ideq
    nemtbir
    pm3.2i
end
