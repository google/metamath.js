include "casa.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "csubrg.mm"
include "clss.mm"
include "cin.mm"
include "crab.mm"
include "cint.mm"
include "eqid.mm"
include "aspval.mm"
include "c0.mm"
include "wne.mm"
include "ssrab2.mm"
include "inss1.mm"
include "sstri.mm"
include "cvv.mm"
include "fvex.mm"
include "syl6eqelr.mm"
include "intex.mm"
include "sylibr.mm"
include "subrgint.mm"
include "sylancr.mm"
include "eqeltrd.mm"

theorem aspsubrg
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


  assert |- ( ( W e. AssAlg /\ S C_ V ) -> ( A ` S ) e. ( SubRing ` W ) )

  proof
    cW
    casa
    wcel
    cS
    cV
    wss
    wa
    #
    cS
    cA
    cfv
    #
    cS
    vt
    cv
    wss
    #
    vt
    cW
    csubrg
    cfv
    #
    cW
    clss
    cfv
    #
    cin
    #
    crab
    #
    cint
    #
    @3
    vt
    cA
    cS
    @4
    cV
    cW
    aspval.a
    aspval.v
    @4
    eqid
    aspval
    #
    @0
    @6
    @3
    wss
    @6
    c0
    wne
    #
    @7
    @3
    wcel
    @6
    @5
    @3
    @2
    vt
    @5
    ssrab2
    @3
    @4
    inss1
    sstri
    @0
    @7
    cvv
    wcel
    @9
    @0
    @7
    @1
    cvv
    @8
    cS
    cA
    fvex
    syl6eqelr
    @6
    intex
    sylibr
    cW
    @6
    subrgint
    sylancr
    eqeltrd
end
