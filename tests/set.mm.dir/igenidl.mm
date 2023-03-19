include "crngo.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cigen.mm"
include "co.mm"
include "cv.mm"
include "cidl.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "igenval.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "rngoidl.mm"
include "sseq2.mm"
include "rspcev.mm"
include "sylan.mm"
include "rabn0.mm"
include "sylibr.mm"
include "ssrab2.mm"
include "intidl.mm"
include "mp3an3.mm"
include "syldan.mm"
include "eqeltrd.mm"

theorem igenidl
  let cR: class R
  let cS: class S
  let cG: class G
  let cX: class X
  let vr: setvar r
  let vs: setvar s
  let vj: setvar j
  assume igenval.1: |- G = ( 1st ` R )
  assume igenval.2: |- X = ran G


  assert |- ( ( R e. RingOps /\ S C_ X ) -> ( R IdlGen S ) e. ( Idl ` R ) )

  proof
    cR
    crngo
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cR
    cS
    cigen
    co
    cS
    vj
    cv
    #
    wss
    #
    vj
    cR
    cidl
    cfv
    #
    crab
    #
    cint
    #
    @5
    cR
    cS
    vj
    cG
    cX
    igenval.1
    igenval.2
    igenval
    @0
    @1
    @6
    c0
    wne
    #
    @7
    @5
    wcel
    #
    @2
    @4
    vj
    @5
    wrex
    #
    @8
    @0
    cX
    @5
    wcel
    @1
    @10
    cR
    cG
    cX
    igenval.1
    igenval.2
    rngoidl
    @4
    @1
    vj
    cX
    @5
    @3
    cX
    cS
    sseq2
    rspcev
    sylan
    @4
    vj
    @5
    rabn0
    sylibr
    @0
    @8
    @6
    @5
    wss
    @9
    @4
    vj
    @5
    ssrab2
    @6
    cR
    intidl
    mp3an3
    syldan
    eqeltrd
end
