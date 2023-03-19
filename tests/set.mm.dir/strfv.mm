include "cstr.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "structex.mm"
include "ax-mp.mm"
include "structfun.mm"
include "cnx.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "wss.mm"
include "opex.mm"
include "snss.mm"
include "mpbir.mm"
include "strfv2.mm"

theorem strfv
  let cC: class C
  let cS: class S
  let cE: class E
  let cV: class V
  let cX: class X
  assume strfv.s: |- S Struct X
  assume strfv.e: |- E = Slot ( E ` ndx )
  assume strfv.n: |- { <. ( E ` ndx ) , C >. } C_ S


  assert |- ( C e. V -> C = ( E ` S ) )

  proof
    cC
    cS
    cE
    cV
    cS
    cX
    cstr
    wbr
    cS
    cvv
    wcel
    strfv.s
    cS
    cX
    structex
    ax-mp
    cS
    cX
    strfv.s
    structfun
    strfv.e
    cnx
    cE
    cfv
    #
    cC
    cop
    #
    cS
    wcel
    @1
    csn
    cS
    wss
    strfv.n
    @1
    cS
    @0
    cC
    opex
    snss
    mpbir
    strfv2
end
