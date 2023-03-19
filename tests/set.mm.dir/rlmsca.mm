include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "crglmod.mm"
include "csca.mm"
include "eqid.mm"
include "ressid.mm"
include "csra.mm"
include "wceq.mm"
include "rlmval.mm"
include "a1i.mm"
include "wss.mm"
include "ssid.mm"
include "srasca.mm"
include "eqtr3d.mm"

theorem rlmsca
  let cR: class R
  let cX: class X


  assert |- ( R e. X -> R = ( Scalar ` ( ringLMod ` R ) ) )

  proof
    cR
    cX
    wcel
    #
    cR
    cR
    cbs
    cfv
    #
    cress
    co
    cR
    cR
    crglmod
    cfv
    #
    csca
    cfv
    @1
    cR
    cX
    @1
    eqid
    ressid
    @0
    @2
    @1
    cR
    @2
    @1
    cR
    csra
    cfv
    cfv
    wceq
    @0
    cR
    rlmval
    a1i
    @1
    @1
    wss
    @0
    @1
    ssid
    a1i
    srasca
    eqtr3d
end
