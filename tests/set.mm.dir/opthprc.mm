include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "cun.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "eleq2.mm"
include "wo.mm"
include "0ex.mm"
include "snid.mm"
include "opelxp.mm"
include "mpbiran2.mm"
include "0nep0.mm"
include "elsn.mm"
include "nemtbir.mm"
include "bianfi.mm"
include "bitr4i.mm"
include "orbi12i.mm"
include "elun.mm"
include "biorfi.mm"
include "3bitr4ri.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "p0ex.mm"
include "eqcom.mm"
include "bitri.mm"
include "wn.mm"
include "wb.mm"
include "biorf.mm"
include "ax-mp.mm"
include "jca.mm"
include "xpeq1.mm"
include "uneq12.mm"
include "syl2an.mm"
include "impbii.mm"

theorem opthprc
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x


  assert |- ( ( ( A X. { (/) } ) u. ( B X. { { (/) } } ) ) = ( ( C X. { (/) } ) u. ( D X. { { (/) } } ) ) <-> ( A = C /\ B = D ) )

  proof
    cA
    c0
    csn
    #
    cxp
    #
    cB
    @0
    csn
    #
    cxp
    #
    cun
    #
    cC
    @0
    cxp
    #
    cD
    @2
    cxp
    #
    cun
    #
    wceq
    #
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wa
    @8
    @9
    @10
    @8
    vx
    cA
    cC
    @8
    vx
    cv
    #
    c0
    cop
    #
    @4
    wcel
    #
    @12
    @7
    wcel
    #
    @11
    cA
    wcel
    #
    @11
    cC
    wcel
    #
    @4
    @7
    @12
    eleq2
    @12
    @1
    wcel
    #
    @12
    @3
    wcel
    #
    wo
    @15
    c0
    @2
    wcel
    #
    wo
    @13
    @15
    @17
    @15
    @18
    @19
    @17
    @15
    c0
    @0
    wcel
    #
    c0
    0ex
    snid
    #
    @11
    c0
    cA
    @0
    opelxp
    mpbiran2
    @18
    @11
    cB
    wcel
    #
    @19
    wa
    @19
    @11
    c0
    cB
    @2
    opelxp
    @19
    @22
    @19
    c0
    @0
    0nep0
    c0
    @0
    0ex
    elsn
    nemtbir
    #
    bianfi
    bitr4i
    orbi12i
    @12
    @1
    @3
    elun
    @19
    @15
    @23
    biorfi
    3bitr4ri
    @12
    @5
    wcel
    #
    @12
    @6
    wcel
    #
    wo
    @16
    @19
    wo
    @14
    @16
    @24
    @16
    @25
    @19
    @24
    @16
    @20
    @21
    @11
    c0
    cC
    @0
    opelxp
    mpbiran2
    @25
    @11
    cD
    wcel
    #
    @19
    wa
    @19
    @11
    c0
    cD
    @2
    opelxp
    @19
    @26
    @23
    bianfi
    bitr4i
    orbi12i
    @12
    @5
    @6
    elun
    @19
    @16
    @23
    biorfi
    3bitr4ri
    3bitr4g
    eqrdv
    @8
    vx
    cB
    cD
    @8
    @11
    @0
    cop
    #
    @4
    wcel
    #
    @27
    @7
    wcel
    #
    @22
    @26
    @4
    @7
    @27
    eleq2
    @27
    @1
    wcel
    #
    @27
    @3
    wcel
    #
    wo
    @0
    @0
    wcel
    #
    @22
    wo
    #
    @28
    @22
    @30
    @32
    @31
    @22
    @30
    @15
    @32
    wa
    @32
    @11
    @0
    cA
    @0
    opelxp
    @32
    @15
    @32
    c0
    @0
    0nep0
    @32
    @0
    c0
    wceq
    c0
    @0
    wceq
    @0
    c0
    p0ex
    elsn
    @0
    c0
    eqcom
    bitri
    nemtbir
    #
    bianfi
    bitr4i
    @31
    @22
    @0
    @2
    wcel
    #
    @0
    p0ex
    snid
    #
    @11
    @0
    cB
    @2
    opelxp
    mpbiran2
    orbi12i
    @27
    @1
    @3
    elun
    @32
    wn
    #
    @22
    @33
    wb
    @34
    @32
    @22
    biorf
    ax-mp
    3bitr4ri
    @27
    @5
    wcel
    #
    @27
    @6
    wcel
    #
    wo
    @32
    @26
    wo
    #
    @29
    @26
    @38
    @32
    @39
    @26
    @38
    @16
    @32
    wa
    @32
    @11
    @0
    cC
    @0
    opelxp
    @32
    @16
    @34
    bianfi
    bitr4i
    @39
    @26
    @35
    @36
    @11
    @0
    cD
    @2
    opelxp
    mpbiran2
    orbi12i
    @27
    @5
    @6
    elun
    @37
    @26
    @40
    wb
    @34
    @32
    @26
    biorf
    ax-mp
    3bitr4ri
    3bitr4g
    eqrdv
    jca
    @9
    @1
    @5
    wceq
    @3
    @6
    wceq
    @8
    @10
    cA
    cC
    @0
    xpeq1
    cB
    cD
    @2
    xpeq1
    @1
    @5
    @3
    @6
    uneq12
    syl2an
    impbii
end
