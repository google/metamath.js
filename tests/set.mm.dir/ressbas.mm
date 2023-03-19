include "cvv.mm"
include "wcel.mm"
include "cin.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "wi.mm"
include "w3a.mm"
include "simp1.mm"
include "sseqin2.mm"
include "sylib.mm"
include "ressid2.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "3expib.mm"
include "wn.mm"
include "cnx.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "simp2.mm"
include "fvex.mm"
include "eqeltri.mm"
include "inex2.mm"
include "baseid.mm"
include "setsid.mm"
include "sylancl.mm"
include "ressval2.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "c0.mm"
include "0fv.mm"
include "0ex.mm"
include "strfvn.mm"
include "in0.mm"
include "3eqtr4ri.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "ineq2d.mm"
include "cress.mm"
include "reldmress.mm"
include "ovprc1.mm"
include "adantr.mm"
include "pm2.61ian.mm"

theorem ressbas
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cW: class W
  let va: setvar a
  let vw: setvar w
  assume ressbas.r: |- R = ( W |`s A )
  assume ressbas.b: |- B = ( Base ` W )


  assert |- ( A e. V -> ( A i^i B ) = ( Base ` R ) )

  proof
    cW
    cvv
    wcel
    #
    cA
    cV
    wcel
    #
    cA
    cB
    cin
    #
    cR
    cbs
    cfv
    #
    wceq
    #
    cB
    cA
    wss
    #
    @0
    @1
    wa
    @4
    wi
    @5
    @0
    @1
    @4
    @5
    @0
    @1
    w3a
    #
    cB
    cW
    cbs
    cfv
    #
    @2
    @3
    ressbas.b
    @6
    @5
    @2
    cB
    wceq
    @5
    @0
    @1
    simp1
    cB
    cA
    sseqin2
    sylib
    @6
    cR
    cW
    cbs
    cA
    cB
    cR
    cW
    cvv
    cV
    ressbas.r
    ressbas.b
    ressid2
    fveq2d
    3eqtr4a
    3expib
    @5
    wn
    #
    @0
    @1
    @4
    @8
    @0
    @1
    w3a
    #
    @2
    cW
    cnx
    cbs
    cfv
    #
    @2
    cop
    csts
    co
    #
    cbs
    cfv
    #
    @3
    @9
    @0
    @2
    cvv
    wcel
    @2
    @12
    wceq
    @8
    @0
    @1
    simp2
    cB
    cA
    cB
    @7
    cvv
    ressbas.b
    cW
    cbs
    fvex
    eqeltri
    inex2
    cvv
    @2
    cbs
    cvv
    cW
    baseid
    setsid
    sylancl
    @9
    cR
    @11
    cbs
    cA
    cB
    cR
    cW
    cvv
    cV
    ressbas.r
    ressbas.b
    ressval2
    fveq2d
    eqtr4d
    3expib
    pm2.61i
    @0
    wn
    #
    @4
    @1
    @13
    cA
    c0
    cin
    #
    c0
    cbs
    cfv
    #
    @2
    @3
    @10
    c0
    cfv
    c0
    @15
    @14
    @10
    0fv
    c0
    cbs
    @10
    0ex
    baseid
    strfvn
    cA
    in0
    3eqtr4ri
    @13
    cB
    c0
    cA
    @13
    cB
    @7
    c0
    ressbas.b
    cW
    cbs
    fvprc
    syl5eq
    ineq2d
    @13
    cR
    c0
    cbs
    @13
    cR
    cW
    cA
    cress
    co
    c0
    ressbas.r
    cW
    cA
    cress
    reldmress
    ovprc1
    syl5eq
    fveq2d
    3eqtr4a
    adantr
    pm2.61ian
end
