include "cvv.mm"
include "cpw.mm"
include "cid.mm"
include "wf1o.mm"
include "wfo.mm"
include "f1ovi.mm"
include "wceq.mm"
include "wb.mm"
include "pwv.mm"
include "f1oeq3.mm"
include "ax-mp.mm"
include "mpbir.mm"
include "f1ofo.mm"

theorem ncanth



  assert |- _I : _V -onto-> ~P _V

  proof
    cvv
    cvv
    cpw
    #
    cid
    wf1o
    #
    cvv
    @0
    cid
    wfo
    @1
    cvv
    cvv
    cid
    wf1o
    #
    f1ovi
    @0
    cvv
    wceq
    @1
    @2
    wb
    pwv
    @0
    cvv
    cvv
    cid
    f1oeq3
    ax-mp
    mpbir
    cvv
    @0
    cid
    f1ofo
    ax-mp
end
