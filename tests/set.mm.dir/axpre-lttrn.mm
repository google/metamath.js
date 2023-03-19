include "cv.mm"
include "c0r.mm"
include "cop.mm"
include "cltrr.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "cnr.mm"
include "cr.mm"
include "elreal.mm"
include "wceq.mm"
include "breq1.mm"
include "anbi1d.mm"
include "imbi12d.mm"
include "breq2.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "anbi2d.mm"
include "wcel.mm"
include "w3a.mm"
include "cltr.mm"
include "ltresr.mm"
include "ltsosr.mm"
include "ltrelsr.mm"
include "sotri.mm"
include "syl2anb.mm"
include "sylibr.mm"
include "a1i.mm"
include "3gencl.mm"

theorem axpre-lttrn
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( ( A <RR B /\ B <RR C ) -> A <RR C ) )

  proof
    vx
    cv
    #
    c0r
    cop
    #
    vy
    cv
    #
    c0r
    cop
    #
    cltrr
    wbr
    #
    @3
    vz
    cv
    #
    c0r
    cop
    #
    cltrr
    wbr
    #
    wa
    #
    @1
    @6
    cltrr
    wbr
    #
    wi
    #
    cA
    @3
    cltrr
    wbr
    #
    @7
    wa
    #
    cA
    @6
    cltrr
    wbr
    #
    wi
    cA
    cB
    cltrr
    wbr
    #
    cB
    @6
    cltrr
    wbr
    #
    wa
    #
    @13
    wi
    @14
    cB
    cC
    cltrr
    wbr
    #
    wa
    #
    cA
    cC
    cltrr
    wbr
    #
    wi
    vx
    vy
    vz
    @1
    @3
    @6
    cA
    cnr
    cr
    cB
    cC
    vx
    cA
    elreal
    vy
    cB
    elreal
    vz
    cC
    elreal
    @1
    cA
    wceq
    #
    @8
    @12
    @9
    @13
    @20
    @4
    @11
    @7
    @1
    cA
    @3
    cltrr
    breq1
    anbi1d
    @1
    cA
    @6
    cltrr
    breq1
    imbi12d
    @3
    cB
    wceq
    #
    @12
    @16
    @13
    @21
    @11
    @14
    @7
    @15
    @3
    cB
    cA
    cltrr
    breq2
    @3
    cB
    @6
    cltrr
    breq1
    anbi12d
    imbi1d
    @6
    cC
    wceq
    #
    @16
    @18
    @13
    @19
    @22
    @15
    @17
    @14
    @6
    cC
    cB
    cltrr
    breq2
    anbi2d
    @6
    cC
    cA
    cltrr
    breq2
    imbi12d
    @10
    @0
    cnr
    wcel
    @2
    cnr
    wcel
    @5
    cnr
    wcel
    w3a
    @8
    @0
    @5
    cltr
    wbr
    #
    @9
    @4
    @0
    @2
    cltr
    wbr
    @2
    @5
    cltr
    wbr
    @23
    @7
    @0
    @2
    ltresr
    @2
    @5
    ltresr
    @0
    @2
    @5
    cltr
    cnr
    ltsosr
    ltrelsr
    sotri
    syl2anb
    @0
    @5
    ltresr
    sylibr
    a1i
    3gencl
end
