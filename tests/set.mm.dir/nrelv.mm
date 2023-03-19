include "cvv.mm"
include "wrel.mm"
include "cxp.mm"
include "wss.mm"
include "c0.mm"
include "wcel.mm"
include "wn.mm"
include "0ex.mm"
include "0nelxp.mm"
include "nelss.mm"
include "mp2an.mm"
include "df-rel.mm"
include "mtbir.mm"

theorem nrelv



  assert |- -. Rel _V

  proof
    cvv
    wrel
    cvv
    cvv
    cvv
    cxp
    #
    wss
    #
    c0
    cvv
    wcel
    c0
    @0
    wcel
    wn
    @1
    wn
    0ex
    cvv
    cvv
    0nelxp
    c0
    cvv
    @0
    nelss
    mp2an
    cvv
    df-rel
    mtbir
end
