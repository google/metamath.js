include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "ccom.mm"
include "wiso.mm"
include "simpl.mm"
include "f1oco.mm"
include "syl2anr.mm"
include "wcel.mm"
include "wf.mm"
include "f1of.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "simprr.mm"
include "simplrr.mm"
include "wceq.mm"
include "breq1.mm"
include "fveq2.mm"
include "breq1d.mm"
include "bibi12d.mm"
include "breq2.mm"
include "breq2d.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "breq12d.mm"
include "bitr4d.mm"
include "bibi2d.mm"
include "2ralbidva.mm"
include "biimpd.mm"
include "impancom.mm"
include "imp.mm"
include "jca.mm"
include "df-isom.mm"
include "anbi12i.mm"
include "3imtr4i.mm"

theorem isotr
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ( H Isom R , S ( A , B ) /\ G Isom S , T ( B , C ) ) -> ( G o. H ) Isom R , T ( A , C ) )

  proof
    cA
    cB
    cH
    wf1o
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @1
    cH
    cfv
    #
    @2
    cH
    cfv
    #
    cS
    wbr
    #
    wb
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    #
    cB
    cC
    cG
    wf1o
    #
    vz
    cv
    #
    vw
    cv
    #
    cS
    wbr
    #
    @11
    cG
    cfv
    #
    @12
    cG
    cfv
    #
    cT
    wbr
    #
    wb
    #
    vw
    cB
    wral
    vz
    cB
    wral
    #
    wa
    #
    wa
    #
    cA
    cC
    cG
    cH
    ccom
    #
    wf1o
    #
    @3
    @1
    @21
    cfv
    #
    @2
    @21
    cfv
    #
    cT
    wbr
    #
    wb
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    cA
    cB
    cR
    cS
    cH
    wiso
    #
    cB
    cC
    cS
    cT
    cG
    wiso
    #
    wa
    cA
    cC
    cR
    cT
    @21
    wiso
    @20
    @22
    @27
    @19
    @10
    @0
    @22
    @9
    @10
    @18
    simpl
    @0
    @8
    simpl
    cA
    cB
    cC
    cG
    cH
    f1oco
    syl2anr
    @9
    @19
    @27
    @0
    @19
    @8
    @27
    @0
    @19
    wa
    #
    @8
    @27
    @30
    @7
    @26
    vx
    vy
    cA
    cA
    @30
    @1
    cA
    wcel
    #
    @2
    cA
    wcel
    #
    wa
    #
    wa
    #
    @6
    @25
    @3
    @34
    @6
    @4
    cG
    cfv
    #
    @5
    cG
    cfv
    #
    cT
    wbr
    #
    @25
    @34
    @4
    cB
    wcel
    @5
    cB
    wcel
    @18
    @6
    @37
    wb
    #
    @34
    cA
    cB
    @1
    cH
    @0
    cA
    cB
    cH
    wf
    #
    @19
    @33
    cA
    cB
    cH
    f1of
    ad2antrr
    #
    @30
    @31
    @32
    simprl
    #
    ffvelrnd
    @34
    cA
    cB
    @2
    cH
    @40
    @30
    @31
    @32
    simprr
    #
    ffvelrnd
    @0
    @10
    @18
    @33
    simplrr
    @17
    @38
    @4
    @12
    cS
    wbr
    #
    @35
    @15
    cT
    wbr
    #
    wb
    vz
    vw
    @4
    @5
    cB
    cB
    @11
    @4
    wceq
    #
    @13
    @43
    @16
    @44
    @11
    @4
    @12
    cS
    breq1
    @45
    @14
    @35
    @15
    cT
    @11
    @4
    cG
    fveq2
    breq1d
    bibi12d
    @12
    @5
    wceq
    #
    @43
    @6
    @44
    @37
    @12
    @5
    @4
    cS
    breq2
    @46
    @15
    @36
    @35
    cT
    @12
    @5
    cG
    fveq2
    breq2d
    bibi12d
    rspc2va
    syl21anc
    @34
    @23
    @35
    @24
    @36
    cT
    @34
    @39
    @31
    @23
    @35
    wceq
    @40
    @41
    cA
    cB
    @1
    cG
    cH
    fvco3
    syl2anc
    @34
    @39
    @32
    @24
    @36
    wceq
    @40
    @42
    cA
    cB
    @2
    cG
    cH
    fvco3
    syl2anc
    breq12d
    bitr4d
    bibi2d
    2ralbidva
    biimpd
    impancom
    imp
    jca
    @28
    @9
    @29
    @19
    vx
    vy
    cA
    cB
    cR
    cS
    cH
    df-isom
    vz
    vw
    cB
    cC
    cS
    cT
    cG
    df-isom
    anbi12i
    vx
    vy
    cA
    cC
    cR
    cT
    @21
    df-isom
    3imtr4i
end
