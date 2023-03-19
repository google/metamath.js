include "clt.mm"
include "cle.mm"
include "cid.mm"
include "cdif.mm"
include "ltrel.mm"
include "wss.mm"
include "wrel.mm"
include "difss.mm"
include "lerel.mm"
include "relss.mm"
include "mp2.mm"
include "cv.mm"
include "wbr.mm"
include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "ltrelxr.mm"
include "brel.mm"
include "cxp.mm"
include "lerelxr.mm"
include "sstri.mm"
include "wn.mm"
include "wne.mm"
include "xrltlen.mm"
include "weq.mm"
include "equcom.mm"
include "vex.mm"
include "ideq.mm"
include "bitr4i.mm"
include "necon3abii.mm"
include "anbi2i.mm"
include "syl6bb.mm"
include "brdif.mm"
include "syl6bbr.mm"
include "pm5.21nii.mm"
include "eqbrriv.mm"

theorem dflt2
  let vx: setvar x
  let vy: setvar y


  assert |- < = ( <_ \ _I )

  proof
    vx
    vy
    clt
    cle
    cid
    cdif
    #
    ltrel
    @0
    cle
    wss
    cle
    wrel
    @0
    wrel
    cle
    cid
    difss
    #
    lerel
    @0
    cle
    relss
    mp2
    vx
    cv
    #
    vy
    cv
    #
    clt
    wbr
    #
    @2
    cxr
    wcel
    @3
    cxr
    wcel
    wa
    #
    @2
    @3
    @0
    wbr
    #
    @2
    @3
    cxr
    cxr
    clt
    ltrelxr
    brel
    @2
    @3
    cxr
    cxr
    @0
    @0
    cle
    cxr
    cxr
    cxp
    @1
    lerelxr
    sstri
    brel
    @5
    @4
    @2
    @3
    cle
    wbr
    #
    @2
    @3
    cid
    wbr
    #
    wn
    #
    wa
    #
    @6
    @5
    @4
    @7
    @3
    @2
    wne
    #
    wa
    @10
    @2
    @3
    xrltlen
    @11
    @9
    @7
    @8
    @3
    @2
    vy
    vx
    weq
    vx
    vy
    weq
    @8
    vy
    vx
    equcom
    @2
    @3
    vy
    vex
    ideq
    bitr4i
    necon3abii
    anbi2i
    syl6bb
    @2
    @3
    cle
    cid
    brdif
    syl6bbr
    pm5.21nii
    eqbrriv
end
