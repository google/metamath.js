include "cfv.mm"
include "cnx.mm"
include "cplusg.mm"
include "ctpos.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "ndxid.mm"
include "wne.mm"
include "c2.mm"
include "ndxarg.mm"
include "plusgndx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "eqid.mm"
include "oppgval.mm"
include "fveq2i.mm"
include "eqtr4i.mm"

theorem oppglem
  let cR: class R
  let cE: class E
  let cN: class N
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume oppgbas.1: |- O = ( oppG ` R )
  assume oppglem.2: |- E = Slot N
  assume oppglem.3: |- N e. NN
  assume oppglem.4: |- N =/= 2


  assert |- ( E ` R ) = ( E ` O )

  proof
    cR
    cE
    cfv
    cR
    cnx
    cplusg
    cfv
    #
    cR
    cplusg
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
    oppglem.2
    oppglem.3
    ndxid
    cnx
    cE
    cfv
    #
    @0
    wne
    cN
    c2
    wne
    oppglem.4
    @4
    cN
    @0
    c2
    cE
    cN
    oppglem.2
    oppglem.3
    ndxarg
    plusgndx
    neeq12i
    mpbir
    setsnid
    cO
    @3
    cE
    @1
    cR
    cO
    @1
    eqid
    oppgbas.1
    oppgval
    fveq2i
    eqtr4i
end
