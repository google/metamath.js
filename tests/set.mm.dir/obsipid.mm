include "cobs.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "c0g.mm"
include "cif.mm"
include "cbs.mm"
include "eqid.mm"
include "obsip.mm"
include "3anidm23.mm"
include "iftruei.mm"
include "syl6eq.mm"

theorem obsipid
  let cA: class A
  let cB: class B
  let c.1: class .1.
  let cF: class F
  let c.xi: class .,
  let cW: class W
  assume obsipid.h: |- ., = ( .i ` W )
  assume obsipid.f: |- F = ( Scalar ` W )
  assume obsipid.u: |- .1. = ( 1r ` F )


  assert |- ( ( B e. ( OBasis ` W ) /\ A e. B ) -> ( A ., A ) = .1. )

  proof
    cB
    cW
    cobs
    cfv
    wcel
    #
    cA
    cB
    wcel
    #
    wa
    cA
    cA
    c.xi
    co
    #
    cA
    cA
    wceq
    #
    c.1
    cF
    c0g
    cfv
    #
    cif
    #
    c.1
    @0
    @1
    @2
    @5
    wceq
    cB
    cA
    cA
    c.1
    cF
    c.xi
    cW
    cbs
    cfv
    #
    cW
    @4
    @6
    eqid
    obsipid.h
    obsipid.f
    obsipid.u
    @4
    eqid
    obsip
    3anidm23
    @3
    c.1
    @4
    cA
    eqid
    iftruei
    syl6eq
end
