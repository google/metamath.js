include "cid.mm"
include "cfv.mm"
include "cbs.mm"
include "cress.mm"
include "co.mm"
include "crglmod.mm"
include "csca.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvi.mm"
include "eqid.mm"
include "ressid.mm"
include "eqtr4d.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "reldmress.mm"
include "ovprc1.mm"
include "pm2.61i.mm"
include "wtru.mm"
include "csra.mm"
include "rlmval.mm"
include "a1i.mm"
include "wss.mm"
include "ssid.mm"
include "srasca.mm"
include "trud.mm"
include "eqtri.mm"

theorem rlmsca2
  let cR: class R


  assert |- ( _I ` R ) = ( Scalar ` ( ringLMod ` R ) )

  proof
    cR
    cid
    cfv
    #
    cR
    cR
    cbs
    cfv
    #
    cress
    co
    #
    cR
    crglmod
    cfv
    #
    csca
    cfv
    #
    cR
    cvv
    wcel
    #
    @0
    @2
    wceq
    @5
    @0
    cR
    @2
    cR
    cvv
    fvi
    @1
    cR
    cvv
    @1
    eqid
    ressid
    eqtr4d
    @5
    wn
    @0
    c0
    @2
    cR
    cid
    fvprc
    cR
    @1
    cress
    reldmress
    ovprc1
    eqtr4d
    pm2.61i
    @2
    @4
    wceq
    wtru
    @3
    @1
    cR
    @3
    @1
    cR
    csra
    cfv
    cfv
    wceq
    wtru
    cR
    rlmval
    a1i
    @1
    @1
    wss
    wtru
    @1
    ssid
    a1i
    srasca
    trud
    eqtri
end
