include "cphl.mm"
include "wcel.mm"
include "wa.mm"
include "cocv.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "cssi.mm"
include "adantl.mm"
include "cbs.mm"
include "wss.mm"
include "ocvss.mm"
include "a1i.mm"
include "ocvlss.mm"
include "sylan2.mm"
include "eqeltrd.mm"

theorem csslss
  let cC: class C
  let cS: class S
  let cL: class L
  let cW: class W
  assume csslss.c: |- C = ( CSubSp ` W )
  assume csslss.l: |- L = ( LSubSp ` W )


  assert |- ( ( W e. PreHil /\ S e. C ) -> S e. L )

  proof
    cW
    cphl
    wcel
    #
    cS
    cC
    wcel
    #
    wa
    cS
    cS
    cW
    cocv
    cfv
    #
    cfv
    #
    @2
    cfv
    #
    cL
    @1
    cS
    @4
    wceq
    @0
    cC
    cS
    @2
    cW
    @2
    eqid
    #
    csslss.c
    cssi
    adantl
    @1
    @0
    @3
    cW
    cbs
    cfv
    #
    wss
    #
    @4
    cL
    wcel
    @7
    @1
    cS
    @2
    @6
    cW
    @6
    eqid
    #
    @5
    ocvss
    a1i
    @3
    cL
    @2
    @6
    cW
    @8
    @5
    csslss.l
    ocvlss
    sylan2
    eqeltrd
end
