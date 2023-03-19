include "cv.mm"
include "cfv.mm"
include "cno.mm"
include "c1.mm"
include "wceq.mm"
include "wi.mm"
include "chst.mm"
include "wral.mm"
include "wss.mm"
include "hstri.mm"
include "wcel.mm"
include "cch.mm"
include "wa.mm"
include "hstles.mm"
include "mpanr1.mm"
include "mpanl2.mm"
include "expcom.mm"
include "ralrimiv.mm"
include "impbii.mm"

theorem hstrbi
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vu: setvar u
  let vx: setvar x
  assume hstr.1: |- A e. CH
  assume hstr.2: |- B e. CH

  disjoint A f
  disjoint B f
  disjoint u x
  disjoint f x
  disjoint A x
  disjoint f u
  disjoint A u
  disjoint B x
  disjoint B u
  assert |- ( A. f e. CHStates ( ( normh ` ( f ` A ) ) = 1 -> ( normh ` ( f ` B ) ) = 1 ) <-> A C_ B )

  proof
    cA
    vf
    cv
    #
    cfv
    cno
    cfv
    c1
    wceq
    cB
    @0
    cfv
    cno
    cfv
    c1
    wceq
    wi
    #
    vf
    chst
    wral
    cA
    cB
    wss
    #
    cA
    cB
    vf
    hstr.1
    hstr.2
    hstri
    @2
    @1
    vf
    chst
    @0
    chst
    wcel
    #
    @2
    @1
    @3
    cA
    cch
    wcel
    #
    @2
    @1
    hstr.1
    @3
    @4
    wa
    cB
    cch
    wcel
    @2
    @1
    hstr.2
    cA
    cB
    @0
    hstles
    mpanr1
    mpanl2
    expcom
    ralrimiv
    impbii
end
