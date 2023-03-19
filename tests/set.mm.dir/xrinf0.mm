include "c0.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cpnf.mm"
include "wceq.mm"
include "wtru.mm"
include "wor.mm"
include "xrltso.mm"
include "a1i.mm"
include "wcel.mm"
include "pnfxr.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "noel.mm"
include "pm2.21i.mm"
include "adantl.mm"
include "wa.mm"
include "wrex.mm"
include "pnfnlt.mm"
include "pm2.21d.mm"
include "imp.mm"
include "eqinfd.mm"
include "trud.mm"

theorem xrinf0
  let vy: setvar y
  let vz: setvar z


  assert |- inf ( (/) , RR* , < ) = +oo

  proof
    c0
    cxr
    clt
    cinf
    cpnf
    wceq
    wtru
    vy
    vz
    cxr
    c0
    cpnf
    clt
    cxr
    clt
    wor
    wtru
    xrltso
    a1i
    cpnf
    cxr
    wcel
    wtru
    pnfxr
    a1i
    vy
    cv
    #
    c0
    wcel
    #
    @0
    cpnf
    clt
    wbr
    wn
    #
    wtru
    @1
    @2
    @0
    noel
    pm2.21i
    adantl
    @0
    cxr
    wcel
    #
    cpnf
    @0
    clt
    wbr
    #
    wa
    vz
    cv
    @0
    clt
    wbr
    vz
    c0
    wrex
    #
    wtru
    @3
    @4
    @5
    @3
    @4
    @5
    @0
    pnfnlt
    pm2.21d
    imp
    adantl
    eqinfd
    trud
end
