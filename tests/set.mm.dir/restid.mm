include "wcel.mm"
include "cvv.mm"
include "cpw.mm"
include "wss.mm"
include "crest.mm"
include "co.mm"
include "wceq.mm"
include "cuni.mm"
include "uniexg.mm"
include "syl5eqel.mm"
include "eqimss2i.mm"
include "sspwuni.mm"
include "mpbir.mm"
include "restid2.mm"
include "sylancl.mm"

theorem restid
  let cJ: class J
  let cV: class V
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  assume restid.1: |- X = U. J


  assert |- ( J e. V -> ( J |`t X ) = J )

  proof
    cJ
    cV
    wcel
    #
    cX
    cvv
    wcel
    cJ
    cX
    cpw
    wss
    #
    cJ
    cX
    crest
    co
    cJ
    wceq
    @0
    cX
    cJ
    cuni
    #
    cvv
    restid.1
    cJ
    cV
    uniexg
    syl5eqel
    @1
    @2
    cX
    wss
    cX
    @2
    restid.1
    eqimss2i
    cJ
    cX
    sspwuni
    mpbir
    cX
    cJ
    cvv
    restid2
    sylancl
end
