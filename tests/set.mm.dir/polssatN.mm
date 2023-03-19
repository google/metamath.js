include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "cfv.mm"
include "cpsubsp.mm"
include "eqid.mm"
include "polsubN.mm"
include "psubssat.mm"
include "syldan.mm"

theorem polssatN
  let cA: class A
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let vp: setvar p
  assume polssat.a: |- A = ( Atoms ` K )
  assume polssat.p: |- ._|_ = ( _|_P ` K )


  assert |- ( ( K e. HL /\ X C_ A ) -> ( ._|_ ` X ) C_ A )

  proof
    cK
    chlt
    wcel
    cX
    cA
    wss
    cX
    c.pe
    cfv
    #
    cK
    cpsubsp
    cfv
    #
    wcel
    @0
    cA
    wss
    cA
    @1
    cK
    c.pe
    cX
    polssat.a
    @1
    eqid
    #
    polssat.p
    polsubN
    cA
    chlt
    @1
    cK
    @0
    polssat.a
    @2
    psubssat
    syldan
end
