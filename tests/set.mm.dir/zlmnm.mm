include "wcel.mm"
include "cnm.mm"
include "cfv.mm"
include "cbs.mm"
include "wceq.mm"
include "eqid.mm"
include "zlmbas.mm"
include "a1i.mm"
include "cplusg.mm"
include "zlmplusg.mm"
include "cds.mm"
include "zlmds.mm"
include "nmpropd.mm"
include "syl5eq.mm"

theorem zlmnm
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  assume zlmlem2.1: |- W = ( ZMod ` G )
  assume zlmnm.1: |- N = ( norm ` G )


  assert |- ( G e. V -> N = ( norm ` W ) )

  proof
    cG
    cV
    wcel
    #
    cN
    cG
    cnm
    cfv
    cW
    cnm
    cfv
    zlmnm.1
    @0
    cG
    cW
    cG
    cbs
    cfv
    #
    cW
    cbs
    cfv
    wceq
    @0
    @1
    cG
    cW
    zlmlem2.1
    @1
    eqid
    zlmbas
    a1i
    cG
    cplusg
    cfv
    #
    cW
    cplusg
    cfv
    wceq
    @0
    @2
    cG
    cW
    zlmlem2.1
    @2
    eqid
    zlmplusg
    a1i
    cG
    cds
    cfv
    #
    cG
    cV
    cW
    zlmlem2.1
    @3
    eqid
    zlmds
    nmpropd
    syl5eq
end
