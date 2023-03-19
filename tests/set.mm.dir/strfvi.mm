include "cfv.mm"
include "cid.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvi.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "wn.mm"
include "c0.mm"
include "str0.mm"
include "fvprc.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem strfvi
  let cS: class S
  let cE: class E
  let cN: class N
  let cX: class X
  assume strfvi.e: |- E = Slot N
  assume strfvi.x: |- X = ( E ` S )


  assert |- X = ( E ` ( _I ` S ) )

  proof
    cX
    cS
    cE
    cfv
    #
    cS
    cid
    cfv
    #
    cE
    cfv
    #
    strfvi.x
    cS
    cvv
    wcel
    #
    @0
    @2
    wceq
    @3
    cS
    @1
    cE
    @3
    @1
    cS
    cS
    cvv
    fvi
    eqcomd
    fveq2d
    @3
    wn
    #
    c0
    c0
    cE
    cfv
    @0
    @2
    cE
    cN
    strfvi.e
    str0
    cS
    cE
    fvprc
    @4
    @1
    c0
    cE
    cS
    cid
    fvprc
    fveq2d
    3eqtr4a
    pm2.61i
    eqtri
end
