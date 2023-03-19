include "cwwlksn.mm"
include "co.mm"
include "wcel.mm"
include "cvv.mm"
include "cn0.mm"
include "cvtx.mm"
include "cfv.mm"
include "cword.mm"
include "w3a.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "cv.mm"
include "cpr.mm"
include "cedg.mm"
include "cc0.mm"
include "cfzo.mm"
include "wral.mm"
include "eqid.mm"
include "wwlknbp.mm"
include "wwlknp.mm"
include "wi.mm"
include "wa.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "3jca.mm"
include "ex.mm"
include "3ad2ant2.mm"
include "sylc.mm"

theorem wwlknbp1
  let cG: class G
  let cN: class N
  let cW: class W
  let vi: setvar i


  assert |- ( W e. ( N WWalksN G ) -> ( N e. NN0 /\ W e. Word ( Vtx ` G ) /\ ( # ` W ) = ( N + 1 ) ) )

  proof
    cW
    cN
    cG
    cwwlksn
    co
    wcel
    cG
    cvv
    wcel
    #
    cN
    cn0
    wcel
    #
    cW
    cG
    cvtx
    cfv
    #
    cword
    wcel
    #
    w3a
    @3
    cW
    chash
    cfv
    cN
    c1
    caddc
    co
    wceq
    #
    vi
    cv
    #
    cW
    cfv
    @5
    c1
    caddc
    co
    cW
    cfv
    cpr
    cG
    cedg
    cfv
    #
    wcel
    vi
    cc0
    cN
    cfzo
    co
    wral
    #
    w3a
    #
    @1
    @3
    @4
    w3a
    #
    cG
    cN
    @2
    cW
    @2
    eqid
    #
    wwlknbp
    vi
    @6
    cG
    cN
    @2
    cW
    @10
    @6
    eqid
    wwlknp
    @1
    @0
    @8
    @9
    wi
    @3
    @1
    @8
    @9
    @1
    @8
    wa
    @1
    @3
    @4
    @1
    @8
    simpl
    @1
    @3
    @4
    @7
    simpr1
    @1
    @3
    @4
    @7
    simpr2
    3jca
    ex
    3ad2ant2
    sylc
end
