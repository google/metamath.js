include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "cltrr.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "cv.mm"
include "c0r.mm"
include "cop.mm"
include "wb.mm"
include "cnr.mm"
include "elreal.mm"
include "wceq.mm"
include "breq1.mm"
include "oveq2.mm"
include "breq1d.mm"
include "bibi12d.mm"
include "breq2.mm"
include "breq2d.mm"
include "oveq1.mm"
include "breq12d.mm"
include "bibi2d.mm"
include "wa.mm"
include "cltr.mm"
include "cplr.mm"
include "ltasr.mm"
include "adantr.mm"
include "ltresr.mm"
include "a1i.mm"
include "addresr.mm"
include "breqan12d.mm"
include "anandis.mm"
include "syl6bb.mm"
include "3bitr4d.mm"
include "ancoms.mm"
include "3impa.mm"
include "3gencl.mm"
include "biimpd.mm"

theorem axpre-ltadd
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( A <RR B -> ( C + A ) <RR ( C + B ) ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cC
    cr
    wcel
    w3a
    cA
    cB
    cltrr
    wbr
    #
    cC
    cA
    caddc
    co
    #
    cC
    cB
    caddc
    co
    #
    cltrr
    wbr
    #
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
    vz
    cv
    #
    c0r
    cop
    #
    @5
    caddc
    co
    #
    @10
    @7
    caddc
    co
    #
    cltrr
    wbr
    #
    wb
    #
    cA
    @7
    cltrr
    wbr
    #
    @10
    cA
    caddc
    co
    #
    @12
    cltrr
    wbr
    #
    wb
    @0
    @16
    @10
    cB
    caddc
    co
    #
    cltrr
    wbr
    #
    wb
    @0
    @3
    wb
    vx
    vy
    vz
    @5
    @7
    @10
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
    @5
    cA
    wceq
    #
    @8
    @15
    @13
    @17
    @5
    cA
    @7
    cltrr
    breq1
    @20
    @11
    @16
    @12
    cltrr
    @5
    cA
    @10
    caddc
    oveq2
    breq1d
    bibi12d
    @7
    cB
    wceq
    #
    @15
    @0
    @17
    @19
    @7
    cB
    cA
    cltrr
    breq2
    @21
    @12
    @18
    @16
    cltrr
    @7
    cB
    @10
    caddc
    oveq2
    breq2d
    bibi12d
    @10
    cC
    wceq
    #
    @19
    @3
    @0
    @22
    @16
    @1
    @18
    @2
    cltrr
    @10
    cC
    cA
    caddc
    oveq1
    @10
    cC
    cB
    caddc
    oveq1
    breq12d
    bibi2d
    @4
    cnr
    wcel
    #
    @6
    cnr
    wcel
    #
    @9
    cnr
    wcel
    #
    @14
    @25
    @23
    @24
    wa
    #
    @14
    @25
    @26
    wa
    #
    @4
    @6
    cltr
    wbr
    #
    @9
    @4
    cplr
    co
    #
    @9
    @6
    cplr
    co
    #
    cltr
    wbr
    #
    @8
    @13
    @25
    @28
    @31
    wb
    @26
    @4
    @6
    @9
    ltasr
    adantr
    @8
    @28
    wb
    @27
    @4
    @6
    ltresr
    a1i
    @27
    @13
    @29
    c0r
    cop
    #
    @30
    c0r
    cop
    #
    cltrr
    wbr
    #
    @31
    @25
    @23
    @24
    @13
    @34
    wb
    @25
    @23
    wa
    @25
    @24
    wa
    @11
    @32
    @12
    @33
    cltrr
    @9
    @4
    addresr
    @9
    @6
    addresr
    breqan12d
    anandis
    @29
    @30
    ltresr
    syl6bb
    3bitr4d
    ancoms
    3impa
    3gencl
    biimpd
end
