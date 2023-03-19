include "cimage.mm"
include "wfun.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "cvv.mm"
include "cxp.mm"
include "cep.mm"
include "ctxp.mm"
include "ccnv.mm"
include "ccom.mm"
include "csymdif.mm"
include "crn.mm"
include "cdif.mm"
include "wss.mm"
include "difss.mm"
include "df-rel.mm"
include "mpbir.mm"
include "df-image.mm"
include "releqi.mm"
include "cima.mm"
include "wceq.mm"
include "vex.mm"
include "brimage.mm"
include "eqtr3.mm"
include "syl2anb.mm"
include "gen2.mm"
include "ax-gen.mm"
include "dffun2.mm"
include "mpbir2an.mm"

theorem funimage
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- Fun Image A

  proof
    cA
    cimage
    #
    wfun
    @0
    wrel
    #
    vx
    cv
    #
    vy
    cv
    #
    @0
    wbr
    #
    @2
    vz
    cv
    #
    @0
    wbr
    #
    wa
    vy
    vz
    weq
    #
    wi
    #
    vz
    wal
    vy
    wal
    #
    vx
    wal
    @1
    cvv
    cvv
    cxp
    #
    cvv
    cep
    ctxp
    cep
    cA
    ccnv
    ccom
    cvv
    ctxp
    csymdif
    crn
    #
    cdif
    #
    wrel
    #
    @13
    @12
    @10
    wss
    @10
    @11
    difss
    @12
    df-rel
    mpbir
    @0
    @12
    cA
    df-image
    releqi
    mpbir
    @9
    vx
    @8
    vy
    vz
    @4
    @3
    cA
    @2
    cima
    #
    wceq
    @5
    @14
    wceq
    @7
    @6
    @2
    @3
    cA
    vx
    vex
    #
    vy
    vex
    brimage
    @2
    @5
    cA
    @15
    vz
    vex
    brimage
    @3
    @5
    @14
    eqtr3
    syl2anb
    gen2
    ax-gen
    vx
    vy
    vz
    @0
    dffun2
    mpbir2an
end
