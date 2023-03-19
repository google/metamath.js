include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "crab.mm"
include "eqid.mm"
include "pmapval.mm"
include "ssrab2.mm"
include "syl6eqss.mm"

theorem pmapssat
  let cA: class A
  let cB: class B
  let cC: class C
  let cK: class K
  let cM: class M
  let cX: class X
  let vp: setvar p
  assume pmapssat.b: |- B = ( Base ` K )
  assume pmapssat.a: |- A = ( Atoms ` K )
  assume pmapssat.m: |- M = ( pmap ` K )


  assert |- ( ( K e. C /\ X e. B ) -> ( M ` X ) C_ A )

  proof
    cK
    cC
    wcel
    cX
    cB
    wcel
    wa
    cX
    cM
    cfv
    vp
    cv
    cX
    cK
    cple
    cfv
    #
    wbr
    #
    vp
    cA
    crab
    cA
    cA
    cB
    cC
    cK
    @0
    cM
    cX
    vp
    pmapssat.b
    @0
    eqid
    pmapssat.a
    pmapssat.m
    pmapval
    @1
    vp
    cA
    ssrab2
    syl6eqss
end
