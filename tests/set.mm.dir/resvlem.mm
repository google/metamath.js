include "wcel.mm"
include "cfv.mm"
include "cvv.mm"
include "wceq.mm"
include "csca.mm"
include "cbs.mm"
include "wss.mm"
include "wa.mm"
include "wi.mm"
include "w3a.mm"
include "eqid.mm"
include "resvid2.mm"
include "fveq2d.mm"
include "3expib.mm"
include "wn.mm"
include "cnx.mm"
include "cress.mm"
include "co.mm"
include "cop.mm"
include "csts.mm"
include "resvval2.mm"
include "ndxid.mm"
include "c5.mm"
include "ndxarg.mm"
include "eqnetri.mm"
include "scandx.mm"
include "neeqtrri.mm"
include "setsnid.mm"
include "syl6eqr.mm"
include "pm2.61i.mm"
include "c0.mm"
include "cresv.mm"
include "reldmresv.mm"
include "ovprc1.mm"
include "syl5eq.mm"
include "str0.mm"
include "fvprc.mm"
include "eqtr4d.mm"
include "adantr.mm"
include "pm2.61ian.mm"
include "syl6reqr.mm"

theorem resvlem
  let cA: class A
  let cC: class C
  let cR: class R
  let cE: class E
  let cN: class N
  let cV: class V
  let cW: class W
  assume resvlem.r: |- R = ( W |`v A )
  assume resvlem.e: |- C = ( E ` W )
  assume resvlem.f: |- E = Slot N
  assume resvlem.n: |- N e. NN
  assume resvlem.b: |- N =/= 5


  assert |- ( A e. V -> C = ( E ` R ) )

  proof
    cA
    cV
    wcel
    #
    cR
    cE
    cfv
    #
    cW
    cE
    cfv
    #
    cC
    cW
    cvv
    wcel
    #
    @0
    @1
    @2
    wceq
    #
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    cA
    wss
    #
    @3
    @0
    wa
    @4
    wi
    @7
    @3
    @0
    @4
    @7
    @3
    @0
    w3a
    cR
    cW
    cE
    cA
    @6
    cR
    @5
    cW
    cvv
    cV
    resvlem.r
    @5
    eqid
    #
    @6
    eqid
    #
    resvid2
    fveq2d
    3expib
    @7
    wn
    #
    @3
    @0
    @4
    @10
    @3
    @0
    w3a
    #
    @1
    cW
    cnx
    csca
    cfv
    #
    @5
    cA
    cress
    co
    #
    cop
    csts
    co
    #
    cE
    cfv
    @2
    @11
    cR
    @14
    cE
    cA
    @6
    cR
    @5
    cW
    cvv
    cV
    resvlem.r
    @8
    @9
    resvval2
    fveq2d
    @13
    @12
    cE
    cW
    cE
    cN
    resvlem.f
    resvlem.n
    ndxid
    cnx
    cE
    cfv
    #
    c5
    @12
    @15
    cN
    c5
    cE
    cN
    resvlem.f
    resvlem.n
    ndxarg
    resvlem.b
    eqnetri
    scandx
    neeqtrri
    setsnid
    syl6eqr
    3expib
    pm2.61i
    @3
    wn
    #
    @4
    @0
    @16
    @1
    c0
    @2
    @16
    @1
    c0
    cE
    cfv
    c0
    @16
    cR
    c0
    cE
    @16
    cR
    cW
    cA
    cresv
    co
    c0
    resvlem.r
    cW
    cA
    cresv
    reldmresv
    ovprc1
    syl5eq
    fveq2d
    cE
    cN
    resvlem.f
    str0
    syl6eqr
    cW
    cE
    fvprc
    eqtr4d
    adantr
    pm2.61ian
    resvlem.e
    syl6reqr
end
