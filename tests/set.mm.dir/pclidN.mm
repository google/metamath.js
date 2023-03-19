include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "catm.mm"
include "wceq.mm"
include "eqid.mm"
include "psubssat.mm"
include "pclvalN.mm"
include "syldan.mm"
include "intmin.mm"
include "adantl.mm"
include "eqtrd.mm"

theorem pclidN
  let cS: class S
  let cU: class U
  let cK: class K
  let cV: class V
  let cX: class X
  let vy: setvar y
  assume pclid.s: |- S = ( PSubSp ` K )
  assume pclid.c: |- U = ( PCl ` K )


  assert |- ( ( K e. V /\ X e. S ) -> ( U ` X ) = X )

  proof
    cK
    cV
    wcel
    #
    cX
    cS
    wcel
    #
    wa
    cX
    cU
    cfv
    #
    cX
    vy
    cv
    wss
    vy
    cS
    crab
    cint
    #
    cX
    @0
    @1
    cX
    cK
    catm
    cfv
    #
    wss
    @2
    @3
    wceq
    @4
    cV
    cS
    cK
    cX
    @4
    eqid
    #
    pclid.s
    psubssat
    vy
    @4
    cS
    cU
    cK
    cV
    cX
    @5
    pclid.s
    pclid.c
    pclvalN
    syldan
    @1
    @3
    cX
    wceq
    @0
    vy
    cX
    cS
    intmin
    adantl
    eqtrd
end
