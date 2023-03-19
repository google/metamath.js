include "wcel.mm"
include "w3a.mm"
include "cun.mm"
include "cdif.mm"
include "cv.mm"
include "wa.mm"
include "wral.mm"
include "simp2.mm"
include "simp3.mm"
include "cpw.mm"
include "c0.mm"
include "isros.mm"
include "simp3bi.mm"
include "3ad2ant1.mm"
include "wceq.mm"
include "uneq1.mm"
include "eleq1d.mm"
include "difeq1.mm"
include "anbi12d.mm"
include "uneq2.mm"
include "difeq2.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "simpld.mm"

theorem unelros
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cS: class S
  let cO: class O
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  assume isros.1: |- Q = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s A. y e. s ( ( x u. y ) e. s /\ ( x \ y ) e. s ) ) }

  disjoint O s
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint A u
  disjoint A v
  disjoint u v
  disjoint B u
  disjoint B v
  disjoint S u
  disjoint S v
  disjoint s u
  disjoint s v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  assert |- ( ( S e. Q /\ A e. S /\ B e. S ) -> ( A u. B ) e. S )

  proof
    cS
    cQ
    wcel
    #
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    w3a
    #
    cA
    cB
    cun
    #
    cS
    wcel
    #
    cA
    cB
    cdif
    #
    cS
    wcel
    #
    @3
    @1
    @2
    vu
    cv
    #
    vv
    cv
    #
    cun
    #
    cS
    wcel
    #
    @8
    @9
    cdif
    #
    cS
    wcel
    #
    wa
    #
    vv
    cS
    wral
    vu
    cS
    wral
    #
    @5
    @7
    wa
    #
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    @0
    @1
    @15
    @2
    @0
    cS
    cO
    cpw
    cpw
    wcel
    c0
    cS
    wcel
    @15
    vx
    vy
    vv
    vu
    cQ
    cS
    cO
    vs
    isros.1
    isros
    simp3bi
    3ad2ant1
    @14
    @16
    cA
    @9
    cun
    #
    cS
    wcel
    #
    cA
    @9
    cdif
    #
    cS
    wcel
    #
    wa
    vu
    vv
    cA
    cB
    cS
    cS
    @8
    cA
    wceq
    #
    @11
    @18
    @13
    @20
    @21
    @10
    @17
    cS
    @8
    cA
    @9
    uneq1
    eleq1d
    @21
    @12
    @19
    cS
    @8
    cA
    @9
    difeq1
    eleq1d
    anbi12d
    @9
    cB
    wceq
    #
    @18
    @5
    @20
    @7
    @22
    @17
    @4
    cS
    @9
    cB
    cA
    uneq2
    eleq1d
    @22
    @19
    @6
    cS
    @9
    cB
    cA
    difeq2
    eleq1d
    anbi12d
    rspc2va
    syl21anc
    simpld
end
