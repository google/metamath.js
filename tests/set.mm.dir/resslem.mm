include "wcel.mm"
include "cfv.mm"
include "cvv.mm"
include "wceq.mm"
include "cbs.mm"
include "wss.mm"
include "wa.mm"
include "wi.mm"
include "w3a.mm"
include "eqid.mm"
include "ressid2.mm"
include "fveq2d.mm"
include "3expib.mm"
include "wn.mm"
include "cnx.mm"
include "cin.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "ressval2.mm"
include "ndxid.mm"
include "c1.mm"
include "ndxarg.mm"
include "1re.mm"
include "gtneii.mm"
include "eqnetri.mm"
include "basendx.mm"
include "neeqtrri.mm"
include "setsnid.mm"
include "syl6eqr.mm"
include "pm2.61i.mm"
include "c0.mm"
include "cress.mm"
include "reldmress.mm"
include "ovprc1.mm"
include "syl5eq.mm"
include "str0.mm"
include "fvprc.mm"
include "eqtr4d.mm"
include "adantr.mm"
include "pm2.61ian.mm"
include "syl6reqr.mm"

theorem resslem
  let cA: class A
  let cC: class C
  let cR: class R
  let cE: class E
  let cN: class N
  let cV: class V
  let cW: class W
  assume resslem.r: |- R = ( W |`s A )
  assume resslem.e: |- C = ( E ` W )
  assume resslem.f: |- E = Slot N
  assume resslem.n: |- N e. NN
  assume resslem.b: |- 1 < N


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
    @6
    @3
    @0
    @4
    @6
    @3
    @0
    w3a
    cR
    cW
    cE
    cA
    @5
    cR
    cW
    cvv
    cV
    resslem.r
    @5
    eqid
    #
    ressid2
    fveq2d
    3expib
    @6
    wn
    #
    @3
    @0
    @4
    @8
    @3
    @0
    w3a
    #
    @1
    cW
    cnx
    cbs
    cfv
    #
    cA
    @5
    cin
    #
    cop
    csts
    co
    #
    cE
    cfv
    @2
    @9
    cR
    @12
    cE
    cA
    @5
    cR
    cW
    cvv
    cV
    resslem.r
    @7
    ressval2
    fveq2d
    @11
    @10
    cE
    cW
    cE
    cN
    resslem.f
    resslem.n
    ndxid
    cnx
    cE
    cfv
    #
    c1
    @10
    @13
    cN
    c1
    cE
    cN
    resslem.f
    resslem.n
    ndxarg
    c1
    cN
    1re
    resslem.b
    gtneii
    eqnetri
    basendx
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
    @14
    @1
    c0
    @2
    @14
    @1
    c0
    cE
    cfv
    c0
    @14
    cR
    c0
    cE
    @14
    cR
    cW
    cA
    cress
    co
    c0
    resslem.r
    cW
    cA
    cress
    reldmress
    ovprc1
    syl5eq
    fveq2d
    cE
    cN
    resslem.f
    str0
    syl6eqr
    cW
    cE
    fvprc
    eqtr4d
    adantr
    pm2.61ian
    resslem.e
    syl6reqr
end
