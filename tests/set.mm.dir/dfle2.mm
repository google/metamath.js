include "cle.mm"
include "clt.mm"
include "cid.mm"
include "cxr.mm"
include "cres.mm"
include "cun.mm"
include "lerel.mm"
include "cxp.mm"
include "wss.mm"
include "wrel.mm"
include "ltrelxr.mm"
include "wf1o.mm"
include "wf.mm"
include "f1oi.mm"
include "f1of.mm"
include "fssxp.mm"
include "mp2b.mm"
include "unssi.mm"
include "relxp.mm"
include "relss.mm"
include "mp2.mm"
include "cv.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "lerelxr.mm"
include "brel.mm"
include "wo.mm"
include "weq.mm"
include "xrleloe.mm"
include "resieq.mm"
include "orbi2d.mm"
include "bitr4d.mm"
include "brun.mm"
include "syl6bbr.mm"
include "pm5.21nii.mm"
include "eqbrriv.mm"

theorem dfle2
  let vx: setvar x
  let vy: setvar y


  assert |- <_ = ( < u. ( _I |` RR* ) )

  proof
    vx
    vy
    cle
    clt
    cid
    cxr
    cres
    #
    cun
    #
    lerel
    @1
    cxr
    cxr
    cxp
    #
    wss
    @2
    wrel
    @1
    wrel
    clt
    @0
    @2
    ltrelxr
    cxr
    cxr
    @0
    wf1o
    cxr
    cxr
    @0
    wf
    @0
    @2
    wss
    cxr
    f1oi
    cxr
    cxr
    @0
    f1of
    cxr
    cxr
    @0
    fssxp
    mp2b
    unssi
    #
    cxr
    cxr
    relxp
    @1
    @2
    relss
    mp2
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    @4
    cxr
    wcel
    @5
    cxr
    wcel
    wa
    #
    @4
    @5
    @1
    wbr
    #
    @4
    @5
    cxr
    cxr
    cle
    lerelxr
    brel
    @4
    @5
    cxr
    cxr
    @1
    @3
    brel
    @7
    @6
    @4
    @5
    clt
    wbr
    #
    @4
    @5
    @0
    wbr
    #
    wo
    #
    @8
    @7
    @6
    @9
    vx
    vy
    weq
    #
    wo
    @11
    @4
    @5
    xrleloe
    @7
    @10
    @12
    @9
    cxr
    @4
    @5
    resieq
    orbi2d
    bitr4d
    @4
    @5
    clt
    @0
    brun
    syl6bbr
    pm5.21nii
    eqbrriv
end
