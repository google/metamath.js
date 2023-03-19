include "cop.mm"
include "csn.mm"
include "cdrng.mm"
include "wcel.mm"
include "c0.mm"
include "cgr.mm"
include "0ngrp.mm"
include "crn.mm"
include "cgi.mm"
include "cfv.mm"
include "cdif.mm"
include "cxp.mm"
include "cres.mm"
include "opex.mm"
include "rnsnop.mm"
include "gidsn.mm"
include "sneqi.mm"
include "difeq12i.mm"
include "difid.mm"
include "eqtri.mm"
include "xpeq2i.mm"
include "xp0.mm"
include "reseq2i.mm"
include "res0.mm"
include "crngo.mm"
include "cvv.mm"
include "wa.mm"
include "wb.mm"
include "snex.mm"
include "isdivrngo.mm"
include "ax-mp.mm"
include "simprbi.mm"
include "syl5eqelr.mm"
include "mto.mm"

theorem zrdivrng
  let cA: class A
  assume zrdivrng.1: |- A e. _V


  assert |- -. <. { <. <. A , A >. , A >. } , { <. <. A , A >. , A >. } >. e. DivRingOps

  proof
    cA
    cA
    cop
    #
    cA
    cop
    #
    csn
    #
    @2
    cop
    #
    cdrng
    wcel
    #
    c0
    cgr
    wcel
    0ngrp
    @4
    c0
    @2
    @2
    crn
    #
    @2
    cgi
    cfv
    #
    csn
    #
    cdif
    #
    @8
    cxp
    #
    cres
    #
    cgr
    @10
    @2
    c0
    cres
    c0
    @9
    c0
    @2
    @9
    @8
    c0
    cxp
    c0
    @8
    c0
    @8
    @8
    cA
    csn
    #
    @11
    cdif
    c0
    @5
    @11
    @7
    @11
    @0
    cA
    cA
    cA
    opex
    rnsnop
    @6
    cA
    cA
    zrdivrng.1
    gidsn
    sneqi
    difeq12i
    @11
    difid
    eqtri
    xpeq2i
    @8
    xp0
    eqtri
    reseq2i
    @2
    res0
    eqtri
    @4
    @3
    crngo
    wcel
    #
    @10
    cgr
    wcel
    #
    @2
    cvv
    wcel
    @4
    @12
    @13
    wa
    wb
    @1
    snex
    cvv
    @2
    @2
    isdivrngo
    ax-mp
    simprbi
    syl5eqelr
    mto
end
