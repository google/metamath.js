include "casa.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "csubrg.mm"
include "cfv.mm"
include "clss.mm"
include "cin.mm"
include "crab.mm"
include "cint.mm"
include "ssintub.mm"
include "eqid.mm"
include "aspval.mm"
include "syl5sseqr.mm"

theorem aspssid
  let cA: class A
  let cS: class S
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let cL: class L
  let cT: class T
  assume aspval.a: |- A = ( AlgSpan ` W )
  assume aspval.v: |- V = ( Base ` W )


  assert |- ( ( W e. AssAlg /\ S C_ V ) -> S C_ ( A ` S ) )

  proof
    cW
    casa
    wcel
    cS
    cV
    wss
    wa
    cS
    vt
    cv
    wss
    vt
    cW
    csubrg
    cfv
    cW
    clss
    cfv
    #
    cin
    #
    crab
    cint
    cS
    cS
    cA
    cfv
    vt
    cS
    @1
    ssintub
    vt
    cA
    cS
    @0
    cV
    cW
    aspval.a
    aspval.v
    @0
    eqid
    aspval
    syl5sseqr
end
