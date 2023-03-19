include "cn.mm"
include "cr.mm"
include "csdm.mm"
include "wbr.mm"
include "cdom.mm"
include "cen.mm"
include "wn.mm"
include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "reex.mm"
include "nnssre.mm"
include "ssdomg.mm"
include "mp2.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "wfo.mm"
include "ruclem13.mm"
include "f1ofo.mm"
include "mto.mm"
include "nex.mm"
include "bren.mm"
include "mtbir.mm"
include "brsdom.mm"
include "mpbir2an.mm"

theorem ruc
  let vf: setvar f


  assert |- NN ~< RR

  proof
    cn
    cr
    csdm
    wbr
    cn
    cr
    cdom
    wbr
    #
    cn
    cr
    cen
    wbr
    #
    wn
    cr
    cvv
    wcel
    cn
    cr
    wss
    @0
    reex
    nnssre
    cn
    cr
    cvv
    ssdomg
    mp2
    @1
    cn
    cr
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @3
    vf
    @3
    cn
    cr
    @2
    wfo
    @2
    ruclem13
    cn
    cr
    @2
    f1ofo
    mto
    nex
    cn
    cr
    vf
    bren
    mtbir
    cn
    cr
    brsdom
    mpbir2an
end
