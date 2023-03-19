include "crg.mm"
include "wcel.mm"
include "casa.mm"
include "cz.mm"
include "cmg.mm"
include "cfv.mm"
include "cmulr.mm"
include "zring.mm"
include "cbs.mm"
include "wceq.mm"
include "eqid.mm"
include "zlmbas.mm"
include "a1i.mm"
include "zlmsca.mm"
include "zringbas.mm"
include "cvsca.mm"
include "zlmvsca.mm"
include "zlmmulr.mm"
include "cabl.mm"
include "clmod.mm"
include "ringabl.mm"
include "zlmlmod.mm"
include "sylib.mm"
include "cplusg.mm"
include "zlmplusg.mm"
include "ringprop.mm"
include "biimpi.mm"
include "ccrg.mm"
include "zringcrng.mm"
include "cv.mm"
include "mulgass2.mm"
include "mulgass3.mm"
include "isassad.mm"
include "assaring.mm"
include "sylibr.mm"
include "impbii.mm"

theorem zlmassa
  let cG: class G
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume zlmlmod.w: |- W = ( ZMod ` G )


  assert |- ( G e. Ring <-> W e. AssAlg )

  proof
    cG
    crg
    wcel
    #
    cW
    casa
    wcel
    #
    @0
    vy
    vz
    cz
    cG
    cmg
    cfv
    #
    cG
    cmulr
    cfv
    #
    zring
    cG
    cbs
    cfv
    #
    cW
    vx
    @4
    cW
    cbs
    cfv
    wceq
    @0
    @4
    cG
    cW
    zlmlmod.w
    @4
    eqid
    #
    zlmbas
    #
    a1i
    cG
    crg
    cW
    zlmlmod.w
    zlmsca
    cz
    zring
    cbs
    cfv
    wceq
    @0
    zringbas
    a1i
    @2
    cW
    cvsca
    cfv
    wceq
    @0
    @2
    cG
    cW
    zlmlmod.w
    @2
    eqid
    #
    zlmvsca
    a1i
    @3
    cW
    cmulr
    cfv
    wceq
    @0
    @3
    cG
    cW
    zlmlmod.w
    @3
    eqid
    #
    zlmmulr
    #
    a1i
    @0
    cG
    cabl
    wcel
    cW
    clmod
    wcel
    cG
    ringabl
    cG
    cW
    zlmlmod.w
    zlmlmod
    sylib
    @0
    cW
    crg
    wcel
    #
    cG
    cW
    @6
    cG
    cplusg
    cfv
    #
    cG
    cW
    zlmlmod.w
    @11
    eqid
    zlmplusg
    @9
    ringprop
    #
    biimpi
    zring
    ccrg
    wcel
    @0
    zringcrng
    a1i
    @4
    cG
    @2
    @3
    vx
    cv
    #
    vy
    cv
    #
    vz
    cv
    #
    @5
    @7
    @8
    mulgass2
    @4
    cG
    @2
    @3
    @13
    @14
    @15
    @5
    @7
    @8
    mulgass3
    isassad
    @1
    @10
    @0
    cW
    assaring
    @12
    sylibr
    impbii
end
