include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "cop.mm"
include "wceq.mm"
include "wcel.mm"
include "ccom.mm"
include "cmpt2.mm"
include "cfv.mm"
include "cxp.mm"
include "cdm.mm"
include "wf1o.mm"
include "wfun.mm"
include "wb.mm"
include "xpcomf1o.mm"
include "f1ofun.mm"
include "funbrfv2b.mm"
include "mp2b.mm"
include "ancom.mm"
include "eqcom.mm"
include "f1odm.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "anbi12i.mm"
include "3bitri.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "exbii.mm"
include "fvex.mm"
include "breq1.mm"
include "anbi2d.mm"
include "ceqsexv.mm"
include "elxp.mm"
include "nfcv.mm"
include "nfmpt22.mm"
include "nfcxfr.mm"
include "nfbr.mm"
include "19.41.mm"
include "nfmpt21.mm"
include "fveq2.mm"
include "opelxpi.mm"
include "csn.mm"
include "ccnv.mm"
include "cuni.mm"
include "sneq.mm"
include "cnveqd.mm"
include "unieqd.mm"
include "opswap.mm"
include "syl6eq.mm"
include "opex.mm"
include "fvmpt.mm"
include "syl.mm"
include "sylan9eq.mm"
include "breq1d.mm"
include "coprab.mm"
include "df-br.mm"
include "df-mpt2.mm"
include "eqtri.mm"
include "oprabid.mm"
include "baib.mm"
include "ancoms.mm"
include "adantl.mm"
include "bitrd.mm"
include "pm5.32da.mm"
include "pm5.32i.mm"
include "bitr3i.mm"
include "3bitr2i.mm"
include "opabbii.mm"
include "df-co.mm"
include "dfoprab2.mm"
include "3eqtr4i.mm"

theorem xpcomco
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume xpcomf1o.1: |- F = ( x e. ( A X. B ) |-> U. `' { x } )
  assume xpcomco.1: |- G = ( y e. B , z e. A |-> C )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint F y
  disjoint F z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint C u
  disjoint C v
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint G u
  disjoint G v
  disjoint G w
  assert |- ( G o. F ) = ( z e. A , y e. B |-> C )

  proof
    vu
    cv
    #
    vw
    cv
    #
    cF
    wbr
    #
    @1
    vv
    cv
    #
    cG
    wbr
    #
    wa
    #
    vw
    wex
    #
    vu
    vv
    copab
    @0
    vz
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    @7
    cA
    wcel
    #
    @8
    cB
    wcel
    #
    wa
    #
    @3
    cC
    wceq
    #
    wa
    #
    wa
    #
    vy
    wex
    #
    vz
    wex
    #
    vu
    vv
    copab
    #
    cG
    cF
    ccom
    vz
    vy
    cA
    cB
    cC
    cmpt2
    #
    @6
    @18
    vu
    vv
    @6
    @1
    @0
    cF
    cfv
    #
    wceq
    #
    @0
    cA
    cB
    cxp
    #
    wcel
    #
    @4
    wa
    #
    wa
    #
    vw
    wex
    @24
    @21
    @3
    cG
    wbr
    #
    wa
    #
    @18
    @5
    @26
    vw
    @5
    @22
    @24
    wa
    #
    @4
    wa
    @26
    @2
    @29
    @4
    @2
    @0
    cF
    cdm
    #
    wcel
    #
    @21
    @1
    wceq
    #
    wa
    #
    @32
    @31
    wa
    @29
    @23
    cB
    cA
    cxp
    #
    cF
    wf1o
    #
    cF
    wfun
    @2
    @33
    wb
    vx
    cA
    cB
    cF
    xpcomf1o.1
    xpcomf1o
    #
    @23
    @34
    cF
    f1ofun
    @0
    @1
    cF
    funbrfv2b
    mp2b
    @31
    @32
    ancom
    @32
    @22
    @31
    @24
    @21
    @1
    eqcom
    @30
    @23
    @0
    @35
    @30
    @23
    wceq
    @36
    @23
    @34
    cF
    f1odm
    ax-mp
    eleq2i
    anbi12i
    3bitri
    anbi1i
    @22
    @24
    @4
    anass
    bitri
    exbii
    @25
    @28
    vw
    @21
    @0
    cF
    fvex
    @22
    @4
    @27
    @24
    @1
    @21
    @3
    cG
    breq1
    anbi2d
    ceqsexv
    @28
    @10
    @13
    wa
    #
    vy
    wex
    #
    vz
    wex
    #
    @27
    wa
    @38
    @27
    wa
    #
    vz
    wex
    @18
    @24
    @39
    @27
    vz
    vy
    @0
    cA
    cB
    elxp
    anbi1i
    @38
    @27
    vz
    vz
    @21
    @3
    cG
    vz
    @21
    nfcv
    vz
    cG
    vy
    vz
    cB
    cA
    cC
    cmpt2
    #
    xpcomco.1
    vy
    vz
    cB
    cA
    cC
    nfmpt22
    nfcxfr
    vz
    @3
    nfcv
    nfbr
    19.41
    @40
    @17
    vz
    @40
    @37
    @27
    wa
    #
    vy
    wex
    @17
    @37
    @27
    vy
    vy
    @21
    @3
    cG
    vy
    @21
    nfcv
    vy
    cG
    @41
    xpcomco.1
    vy
    vz
    cB
    cA
    cC
    nfmpt21
    nfcxfr
    vy
    @3
    nfcv
    nfbr
    19.41
    @42
    @16
    vy
    @42
    @10
    @13
    @27
    wa
    #
    wa
    @16
    @10
    @13
    @27
    anass
    @10
    @43
    @15
    @10
    @13
    @27
    @14
    @37
    @27
    @8
    @7
    cop
    #
    @3
    cG
    wbr
    #
    @14
    @37
    @21
    @44
    @3
    cG
    @10
    @13
    @21
    @9
    cF
    cfv
    #
    @44
    @0
    @9
    cF
    fveq2
    @13
    @9
    @23
    wcel
    @46
    @44
    wceq
    @7
    @8
    cA
    cB
    opelxpi
    vx
    @9
    vx
    cv
    #
    csn
    #
    ccnv
    #
    cuni
    #
    @44
    @23
    cF
    @47
    @9
    wceq
    #
    @50
    @9
    csn
    #
    ccnv
    #
    cuni
    @44
    @51
    @49
    @53
    @51
    @48
    @52
    @47
    @9
    sneq
    cnveqd
    unieqd
    @7
    @8
    opswap
    syl6eq
    xpcomf1o.1
    @8
    @7
    opex
    fvmpt
    syl
    sylan9eq
    breq1d
    @13
    @45
    @14
    wb
    #
    @10
    @12
    @11
    @54
    @45
    @12
    @11
    wa
    #
    @14
    @45
    @44
    @3
    cop
    #
    cG
    wcel
    @56
    @55
    @14
    wa
    #
    vy
    vz
    vv
    coprab
    #
    wcel
    @57
    @44
    @3
    cG
    df-br
    cG
    @58
    @56
    cG
    @41
    @58
    xpcomco.1
    vy
    vz
    vv
    cB
    cA
    cC
    df-mpt2
    eqtri
    eleq2i
    @57
    vy
    vz
    vv
    oprabid
    3bitri
    baib
    ancoms
    adantl
    bitrd
    pm5.32da
    pm5.32i
    bitri
    exbii
    bitr3i
    exbii
    3bitr2i
    3bitri
    opabbii
    vu
    vv
    vw
    cG
    cF
    df-co
    @20
    @15
    vz
    vy
    vv
    coprab
    @19
    vz
    vy
    vv
    cA
    cB
    cC
    df-mpt2
    @15
    vz
    vy
    vv
    vu
    dfoprab2
    eqtri
    3eqtr4i
end
