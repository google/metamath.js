include "crngo.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cidl.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "cigen.mm"
include "co.mm"
include "ssintub.mm"
include "igenval.mm"
include "syl5sseqr.mm"

theorem igenss
  let cR: class R
  let cS: class S
  let cG: class G
  let cX: class X
  let vr: setvar r
  let vs: setvar s
  let vj: setvar j
  assume igenval.1: |- G = ( 1st ` R )
  assume igenval.2: |- X = ran G


  assert |- ( ( R e. RingOps /\ S C_ X ) -> S C_ ( R IdlGen S ) )

  proof
    cR
    crngo
    wcel
    cS
    cX
    wss
    wa
    cS
    vj
    cv
    wss
    vj
    cR
    cidl
    cfv
    #
    crab
    cint
    cS
    cR
    cS
    cigen
    co
    vj
    cS
    @0
    ssintub
    cR
    cS
    vj
    cG
    cX
    igenval.1
    igenval.2
    igenval
    syl5sseqr
end
