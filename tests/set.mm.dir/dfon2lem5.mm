include "cv.mm"
include "wpss.mm"
include "wtr.mm"
include "wa.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wceq.mm"
include "wn.mm"
include "wo.mm"
include "w3o.mm"
include "wss.mm"
include "dfon2lem4.mm"
include "dfpss2.mm"
include "eqcom.mm"
include "notbii.mm"
include "anbi2i.mm"
include "bitri.mm"
include "orbi12i.mm"
include "andir.mm"
include "bitr4i.mm"
include "orcom.mm"
include "wel.mm"
include "wral.mm"
include "cvv.mm"
include "dfon2lem3.mm"
include "ax-mp.mm"
include "simpld.mm"
include "psseq1.mm"
include "treq.mm"
include "anbi12d.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "spcv.mm"
include "expcomd.mm"
include "imp.mm"
include "sylan2.mm"
include "mpan9.mm"
include "orim12d.mm"
include "syl5bi.mm"
include "syl5bir.mm"
include "mpand.mm"
include "3orrot.mm"
include "3orass.mm"
include "df-or.mm"
include "sylibr.mm"

theorem dfon2lem5
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume dfon2lem5.1: |- A e. _V
  assume dfon2lem5.2: |- B e. _V

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint B z
  assert |- ( ( A. x ( ( x C. A /\ Tr x ) -> x e. A ) /\ A. y ( ( y C. B /\ Tr y ) -> y e. B ) ) -> ( A e. B \/ A = B \/ B e. A ) )

  proof
    vx
    cv
    #
    cA
    wpss
    #
    @0
    wtr
    #
    wa
    #
    @0
    cA
    wcel
    #
    wi
    #
    vx
    wal
    #
    vy
    cv
    #
    cB
    wpss
    #
    @7
    wtr
    #
    wa
    #
    @7
    cB
    wcel
    #
    wi
    #
    vy
    wal
    #
    wa
    #
    cA
    cB
    wceq
    #
    wn
    #
    cB
    cA
    wcel
    #
    cA
    cB
    wcel
    #
    wo
    #
    wi
    #
    @18
    @15
    @17
    w3o
    #
    @14
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wo
    #
    @16
    @19
    vx
    vy
    cA
    cB
    dfon2lem5.1
    dfon2lem5.2
    dfon2lem4
    @24
    @16
    wa
    #
    cA
    cB
    wpss
    #
    cB
    cA
    wpss
    #
    wo
    #
    @14
    @19
    @28
    @22
    @16
    wa
    #
    @23
    @16
    wa
    #
    wo
    @25
    @26
    @29
    @27
    @30
    cA
    cB
    dfpss2
    @27
    @23
    cB
    cA
    wceq
    #
    wn
    #
    wa
    @30
    cB
    cA
    dfpss2
    @32
    @16
    @23
    @31
    @15
    cB
    cA
    eqcom
    notbii
    anbi2i
    bitri
    orbi12i
    @22
    @23
    @16
    andir
    bitr4i
    @28
    @27
    @26
    wo
    @14
    @19
    @26
    @27
    orcom
    @14
    @27
    @17
    @26
    @18
    @13
    @6
    cB
    wtr
    #
    @27
    @17
    wi
    #
    @13
    @33
    vz
    vz
    wel
    wn
    #
    vz
    cB
    wral
    #
    cB
    cvv
    wcel
    @13
    @33
    @36
    wa
    wi
    dfon2lem5.2
    vy
    vz
    cB
    cvv
    dfon2lem3
    ax-mp
    simpld
    @6
    @33
    @34
    @6
    @27
    @33
    @17
    @5
    @27
    @33
    wa
    #
    @17
    wi
    vx
    cB
    dfon2lem5.2
    @0
    cB
    wceq
    #
    @3
    @37
    @4
    @17
    @38
    @1
    @27
    @2
    @33
    @0
    cB
    cA
    psseq1
    @0
    cB
    treq
    anbi12d
    @0
    cB
    cA
    eleq1
    imbi12d
    spcv
    expcomd
    imp
    sylan2
    @6
    cA
    wtr
    #
    @13
    @26
    @18
    wi
    @6
    @39
    @35
    vz
    cA
    wral
    #
    cA
    cvv
    wcel
    @6
    @39
    @40
    wa
    wi
    dfon2lem5.1
    vx
    vz
    cA
    cvv
    dfon2lem3
    ax-mp
    simpld
    @13
    @26
    @39
    @18
    @12
    @26
    @39
    wa
    #
    @18
    wi
    vy
    cA
    dfon2lem5.1
    @7
    cA
    wceq
    #
    @10
    @41
    @11
    @18
    @42
    @8
    @26
    @9
    @39
    @7
    cA
    cB
    psseq1
    @7
    cA
    treq
    anbi12d
    @7
    cA
    cB
    eleq1
    imbi12d
    spcv
    expcomd
    mpan9
    orim12d
    syl5bi
    syl5bir
    mpand
    @21
    @15
    @17
    @18
    w3o
    #
    @20
    @18
    @15
    @17
    3orrot
    @43
    @15
    @19
    wo
    @20
    @15
    @17
    @18
    3orass
    @15
    @19
    df-or
    bitri
    bitri
    sylibr
end
