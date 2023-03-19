include "cfv.mm"
include "cnx.mm"
include "cmulr.mm"
include "ctpos.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "ndxid.mm"
include "wne.mm"
include "c3.mm"
include "nnrei.mm"
include "ltneii.mm"
include "ndxarg.mm"
include "mulrndx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "cbs.mm"
include "eqid.mm"
include "opprval.mm"
include "fveq2i.mm"
include "eqtr4i.mm"

theorem opprlem
  let cR: class R
  let cE: class E
  let cN: class N
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume opprbas.1: |- O = ( oppR ` R )
  assume opprlem.2: |- E = Slot N
  assume opprlem.3: |- N e. NN
  assume opprlem.4: |- N < 3


  assert |- ( E ` R ) = ( E ` O )

  proof
    cR
    cE
    cfv
    cR
    cnx
    cmulr
    cfv
    #
    cR
    cmulr
    cfv
    #
    ctpos
    #
    cop
    csts
    co
    #
    cE
    cfv
    cO
    cE
    cfv
    @2
    @0
    cE
    cR
    cE
    cN
    opprlem.2
    opprlem.3
    ndxid
    cnx
    cE
    cfv
    #
    @0
    wne
    cN
    c3
    wne
    cN
    c3
    cN
    opprlem.3
    nnrei
    opprlem.4
    ltneii
    @4
    cN
    @0
    c3
    cE
    cN
    opprlem.2
    opprlem.3
    ndxarg
    mulrndx
    neeq12i
    mpbir
    setsnid
    cO
    @3
    cE
    cR
    cbs
    cfv
    #
    cR
    @1
    cO
    @5
    eqid
    @1
    eqid
    opprbas.1
    opprval
    fveq2i
    eqtr4i
end
