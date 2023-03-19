include "cfn.mm"
include "wcel.mm"
include "ccrd.mm"
include "cfv.mm"
include "cvv.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "cc0.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "chash.mm"
include "cardidm.mm"
include "fveq2i.mm"
include "wceq.mm"
include "wss.mm"
include "ficardom.mm"
include "ssid.mm"
include "ssnnfi.mm"
include "sylancl.mm"
include "eqid.mm"
include "hashgval.mm"
include "syl.mm"
include "3eqtr3a.mm"

theorem hashcard
  let cA: class A
  let vx: setvar x


  assert |- ( A e. Fin -> ( # ` ( card ` A ) ) = ( # ` A ) )

  proof
    cA
    cfn
    wcel
    #
    cA
    ccrd
    cfv
    #
    ccrd
    cfv
    #
    vx
    cvv
    vx
    cv
    c1
    caddc
    co
    cmpt
    cc0
    crdg
    com
    cres
    #
    cfv
    #
    @1
    @3
    cfv
    @1
    chash
    cfv
    #
    cA
    chash
    cfv
    @2
    @1
    @3
    cA
    cardidm
    fveq2i
    @0
    @1
    cfn
    wcel
    #
    @4
    @5
    wceq
    @0
    @1
    com
    wcel
    @1
    @1
    wss
    @6
    cA
    ficardom
    @1
    ssid
    @1
    @1
    ssnnfi
    sylancl
    vx
    @1
    @3
    @3
    eqid
    #
    hashgval
    syl
    vx
    cA
    @3
    @7
    hashgval
    3eqtr3a
end
