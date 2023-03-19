include "cfv.mm"
include "cnx.mm"
include "cplusg.mm"
include "cmulr.mm"
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
include "mgpval.mm"
include "fveq2i.mm"
include "eqtr4i.mm"

theorem mgplem
  let cR: class R
  let cE: class E
  let cM: class M
  let cN: class N
  assume mgpbas.1: |- M = ( mulGrp ` R )
  assume mgplem.2: |- E = Slot N
  assume mgplem.3: |- N e. NN
  assume mgplem.4: |- N =/= 2


  assert |- ( E ` R ) = ( E ` M )

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
    cmulr
    cfv
    #
    cop
    csts
    co
    #
    cE
    cfv
    cM
    cE
    cfv
    @1
    @0
    cE
    cR
    cE
    cN
    mgplem.2
    mgplem.3
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
    mgplem.4
    @3
    cN
    @0
    c2
    cE
    cN
    mgplem.2
    mgplem.3
    ndxarg
    plusgndx
    neeq12i
    mpbir
    setsnid
    cM
    @2
    cE
    cR
    @1
    cM
    mgpbas.1
    @1
    eqid
    mgpval
    fveq2i
    eqtr4i
end
