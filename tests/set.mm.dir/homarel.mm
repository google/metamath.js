include "co.mm"
include "wrel.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "xpss.mm"
include "cpw.mm"
include "eqid.mm"
include "homarcl.mm"
include "homaf.mm"
include "homarcl2.mm"
include "simpld.mm"
include "simprd.mm"
include "fovrnd.mm"
include "elelpwi.mm"
include "mpdan.mm"
include "sseldi.mm"
include "ssriv.mm"
include "df-rel.mm"
include "mpbir.mm"

theorem homarel
  let cC: class C
  let cH: class H
  let cX: class X
  let cY: class Y
  let vf: setvar f
  assume homahom.h: |- H = ( HomA ` C )


  assert |- Rel ( X H Y )

  proof
    cX
    cY
    cH
    co
    #
    wrel
    @0
    cvv
    cvv
    cxp
    #
    wss
    vf
    @0
    @1
    vf
    cv
    #
    @0
    wcel
    #
    cC
    cbs
    cfv
    #
    @4
    cxp
    #
    cvv
    cxp
    #
    @1
    @2
    @5
    cvv
    xpss
    @3
    @0
    @6
    cpw
    #
    wcel
    @2
    @6
    wcel
    @3
    cX
    cY
    @7
    @4
    @4
    cH
    @3
    @4
    cC
    cH
    homahom.h
    @4
    eqid
    #
    cC
    @2
    cH
    cX
    cY
    homahom.h
    homarcl
    homaf
    @3
    cX
    @4
    wcel
    #
    cY
    @4
    wcel
    #
    @4
    cC
    @2
    cH
    cX
    cY
    homahom.h
    @8
    homarcl2
    #
    simpld
    @3
    @9
    @10
    @11
    simprd
    fovrnd
    @2
    @0
    @6
    elelpwi
    mpdan
    sseldi
    ssriv
    @0
    df-rel
    mpbir
end
