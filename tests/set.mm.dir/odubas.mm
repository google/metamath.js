include "cbs.mm"
include "cfv.mm"
include "cnx.mm"
include "cple.mm"
include "ccnv.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "baseid.mm"
include "wne.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "1re.mm"
include "1lt10.mm"
include "ltneii.mm"
include "basendx.mm"
include "plendx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "eqid.mm"
include "oduval.mm"
include "fveq2i.mm"
include "3eqtr4i.mm"

theorem odubas
  let cB: class B
  let cD: class D
  let cO: class O
  let va: setvar a
  let c.le: class .<_
  let cG: class G
  let cA: class A
  assume oduval.d: |- D = ( ODual ` O )
  assume odubas.b: |- B = ( Base ` O )


  assert |- B = ( Base ` D )

  proof
    cO
    cbs
    cfv
    cO
    cnx
    cple
    cfv
    #
    cO
    cple
    cfv
    #
    ccnv
    #
    cop
    csts
    co
    #
    cbs
    cfv
    cB
    cD
    cbs
    cfv
    @2
    @0
    cbs
    cO
    baseid
    cnx
    cbs
    cfv
    #
    @0
    wne
    c1
    c1
    cc0
    cdc
    #
    wne
    c1
    @5
    1re
    1lt10
    ltneii
    @4
    c1
    @0
    @5
    basendx
    plendx
    neeq12i
    mpbir
    setsnid
    odubas.b
    cD
    @3
    cbs
    cD
    @1
    cO
    oduval.d
    @1
    eqid
    oduval
    fveq2i
    3eqtr4i
end
