include "wcel.mm"
include "cpw.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "wss.mm"
include "eleq1.mm"
include "raleqbi1dv.mm"
include "elrab2.mm"
include "cvv.mm"
include "wb.mm"
include "c0.mm"
include "wceq.mm"
include "0ex.mm"
include "mpbiri.mm"
include "adantl.mm"
include "wne.mm"
include "elex.mm"
include "ralimi.mm"
include "r19.3rzv.mm"
include "biimparc.mm"
include "sylan.mm"
include "pm2.61dane.mm"
include "elpwg.mm"
include "syl.mm"
include "pm5.32ri.mm"
include "bitri.mm"

theorem neipeltop
  let cC: class C
  let cJ: class J
  let cN: class N
  let cX: class X
  let vp: setvar p
  let va: setvar a
  assume neiptop.o: |- J = { a e. ~P X | A. p e. a a e. ( N ` p ) }

  disjoint a p
  disjoint C a
  disjoint C p
  disjoint N a
  disjoint X a
  assert |- ( C e. J <-> ( C C_ X /\ A. p e. C C e. ( N ` p ) ) )

  proof
    cC
    cJ
    wcel
    cC
    cX
    cpw
    #
    wcel
    #
    cC
    vp
    cv
    cN
    cfv
    #
    wcel
    #
    vp
    cC
    wral
    #
    wa
    cC
    cX
    wss
    #
    @4
    wa
    va
    cv
    #
    @2
    wcel
    #
    vp
    @6
    wral
    @4
    va
    cC
    @0
    cJ
    @7
    @3
    vp
    @6
    cC
    @6
    cC
    @2
    eleq1
    raleqbi1dv
    neiptop.o
    elrab2
    @4
    @1
    @5
    @4
    cC
    cvv
    wcel
    #
    @1
    @5
    wb
    @4
    @8
    cC
    c0
    cC
    c0
    wceq
    #
    @8
    @4
    @9
    @8
    c0
    cvv
    wcel
    0ex
    cC
    c0
    cvv
    eleq1
    mpbiri
    adantl
    @4
    @8
    vp
    cC
    wral
    #
    cC
    c0
    wne
    #
    @8
    @3
    @8
    vp
    cC
    cC
    @2
    elex
    ralimi
    @11
    @8
    @10
    @8
    vp
    cC
    r19.3rzv
    biimparc
    sylan
    pm2.61dane
    cC
    cX
    cvv
    elpwg
    syl
    pm5.32ri
    bitri
end
