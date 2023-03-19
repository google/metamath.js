include "cc0.mm"
include "cv.mm"
include "c0r.mm"
include "cop.mm"
include "cltrr.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "wi.mm"
include "cnr.mm"
include "cr.mm"
include "elreal.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi1d.mm"
include "oveq1.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "wcel.mm"
include "cmr.mm"
include "cltr.mm"
include "df-0.mm"
include "breq1i.mm"
include "ltresr.mm"
include "bitri.mm"
include "mulgt0sr.mm"
include "syl2anb.mm"
include "a1i.mm"
include "mulresr.mm"
include "breq12d.mm"
include "syl6bb.mm"
include "syl5ibr.mm"
include "2gencl.mm"

theorem axpre-mulgt0
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( 0 <RR A /\ 0 <RR B ) -> 0 <RR ( A x. B ) ) )

  proof
    cc0
    vx
    cv
    #
    c0r
    cop
    #
    cltrr
    wbr
    #
    cc0
    vy
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
    cc0
    @1
    @4
    cmul
    co
    #
    cltrr
    wbr
    #
    wi
    cc0
    cA
    cltrr
    wbr
    #
    @5
    wa
    #
    cc0
    cA
    @4
    cmul
    co
    #
    cltrr
    wbr
    #
    wi
    @9
    cc0
    cB
    cltrr
    wbr
    #
    wa
    #
    cc0
    cA
    cB
    cmul
    co
    #
    cltrr
    wbr
    #
    wi
    vx
    vy
    @1
    @4
    cA
    cB
    cnr
    cr
    vx
    cA
    elreal
    vy
    cB
    elreal
    @1
    cA
    wceq
    #
    @6
    @10
    @8
    @12
    @17
    @2
    @9
    @5
    @1
    cA
    cc0
    cltrr
    breq2
    anbi1d
    @17
    @7
    @11
    cc0
    cltrr
    @1
    cA
    @4
    cmul
    oveq1
    breq2d
    imbi12d
    @4
    cB
    wceq
    #
    @10
    @14
    @12
    @16
    @18
    @5
    @13
    @9
    @4
    cB
    cc0
    cltrr
    breq2
    anbi2d
    @18
    @11
    @15
    cc0
    cltrr
    @4
    cB
    cA
    cmul
    oveq2
    breq2d
    imbi12d
    @6
    @8
    @0
    cnr
    wcel
    @3
    cnr
    wcel
    wa
    #
    c0r
    @0
    @3
    cmr
    co
    #
    cltr
    wbr
    #
    @2
    c0r
    @0
    cltr
    wbr
    #
    c0r
    @3
    cltr
    wbr
    #
    @21
    @5
    @2
    c0r
    c0r
    cop
    #
    @1
    cltrr
    wbr
    @22
    cc0
    @24
    @1
    cltrr
    df-0
    breq1i
    c0r
    @0
    ltresr
    bitri
    @5
    @24
    @4
    cltrr
    wbr
    @23
    cc0
    @24
    @4
    cltrr
    df-0
    breq1i
    c0r
    @3
    ltresr
    bitri
    @0
    @3
    mulgt0sr
    syl2anb
    @19
    @8
    @24
    @20
    c0r
    cop
    #
    cltrr
    wbr
    @21
    @19
    cc0
    @24
    @7
    @25
    cltrr
    cc0
    @24
    wceq
    @19
    df-0
    a1i
    @0
    @3
    mulresr
    breq12d
    c0r
    @20
    ltresr
    syl6bb
    syl5ibr
    2gencl
end
