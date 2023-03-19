include "casa.mm"
include "wcel.mm"
include "csubrg.mm"
include "cfv.mm"
include "w3a.mm"
include "cv.mm"
include "wss.mm"
include "cin.mm"
include "crab.mm"
include "cint.mm"
include "wceq.mm"
include "simp1.mm"
include "subrgss.mm"
include "3ad2ant2.mm"
include "aspval.mm"
include "syl2anc.mm"
include "wa.mm"
include "3simpc.mm"
include "elin.mm"
include "sylibr.mm"
include "intmin.mm"
include "syl.mm"
include "eqtrd.mm"

theorem aspid
  let cA: class A
  let cS: class S
  let cL: class L
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let cT: class T
  assume aspval.a: |- A = ( AlgSpan ` W )
  assume aspval.v: |- V = ( Base ` W )
  assume aspval.l: |- L = ( LSubSp ` W )


  assert |- ( ( W e. AssAlg /\ S e. ( SubRing ` W ) /\ S e. L ) -> ( A ` S ) = S )

  proof
    cW
    casa
    wcel
    #
    cS
    cW
    csubrg
    cfv
    #
    wcel
    #
    cS
    cL
    wcel
    #
    w3a
    #
    cS
    cA
    cfv
    #
    cS
    vt
    cv
    wss
    vt
    @1
    cL
    cin
    #
    crab
    cint
    #
    cS
    @4
    @0
    cS
    cV
    wss
    #
    @5
    @7
    wceq
    @0
    @2
    @3
    simp1
    @2
    @0
    @8
    @3
    cS
    cV
    cW
    aspval.v
    subrgss
    3ad2ant2
    vt
    cA
    cS
    cL
    cV
    cW
    aspval.a
    aspval.v
    aspval.l
    aspval
    syl2anc
    @4
    cS
    @6
    wcel
    #
    @7
    cS
    wceq
    @4
    @2
    @3
    wa
    @9
    @0
    @2
    @3
    3simpc
    cS
    @1
    cL
    elin
    sylibr
    vt
    cS
    @6
    intmin
    syl
    eqtrd
end
