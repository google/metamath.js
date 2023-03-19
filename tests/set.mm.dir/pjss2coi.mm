include "wss.mm"
include "cpjh.mm"
include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "cv.mm"
include "chil.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "pjcoi.mm"
include "adantl.mm"
include "wi.mm"
include "c0v.mm"
include "cif.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "ifhvhv0.mm"
include "pjss2i.mm"
include "dedth.mm"
include "impcom.mm"
include "eqtrd.mm"
include "ralrimiva.mm"
include "pjfi.mm"
include "hocofi.mm"
include "hoeqi.mm"
include "sylib.mm"
include "csp.mm"
include "co.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "ad2antlr.mm"
include "pjadjcoi.mm"
include "adantlr.mm"
include "pjadji.mm"
include "3eqtr4d.mm"
include "exp31.mm"
include "ralrimdv.mm"
include "wb.mm"
include "pjcohcli.mm"
include "pjhcli.mm"
include "hial2eq.mm"
include "syl2anc.mm"
include "sylibd.mm"
include "com12.mm"
include "ralrimiv.mm"
include "pjss1coi.mm"
include "sylibr.mm"
include "impbii.mm"

theorem pjss2coi
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjco.1: |- G e. CH
  assume pjco.2: |- H e. CH


  assert |- ( G C_ H <-> ( ( projh ` G ) o. ( projh ` H ) ) = ( projh ` G ) )

  proof
    cG
    cH
    wss
    #
    cG
    cpjh
    cfv
    #
    cH
    cpjh
    cfv
    #
    ccom
    #
    @1
    wceq
    #
    @0
    vx
    cv
    #
    @3
    cfv
    #
    @5
    @1
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    @4
    @0
    @8
    vx
    chil
    @0
    @5
    chil
    wcel
    #
    wa
    @6
    @5
    @2
    cfv
    #
    @1
    cfv
    #
    @7
    @9
    @6
    @11
    wceq
    @0
    @5
    cG
    cH
    pjco.1
    pjco.2
    pjcoi
    adantl
    @9
    @0
    @11
    @7
    wceq
    #
    @9
    @0
    @12
    wi
    @0
    @9
    @5
    c0v
    cif
    #
    @2
    cfv
    #
    @1
    cfv
    #
    @13
    @1
    cfv
    #
    wceq
    #
    wi
    @5
    c0v
    @5
    @13
    wceq
    #
    @12
    @17
    @0
    @18
    @11
    @15
    @7
    @16
    @18
    @10
    @14
    @1
    @5
    @13
    @2
    fveq2
    fveq2d
    @5
    @13
    @1
    fveq2
    eqeq12d
    imbi2d
    @13
    cH
    cG
    pjco.1
    @5
    ifhvhv0
    pjco.2
    pjss2i
    dedth
    impcom
    eqtrd
    ralrimiva
    vx
    @3
    @1
    @1
    @2
    cG
    pjco.1
    pjfi
    #
    cH
    pjco.2
    pjfi
    #
    hocofi
    @19
    hoeqi
    sylib
    @4
    @2
    @1
    ccom
    #
    @1
    wceq
    #
    @0
    @4
    @5
    @21
    cfv
    #
    @7
    wceq
    #
    vx
    chil
    wral
    @22
    @4
    @24
    vx
    chil
    @9
    @4
    @24
    @9
    @4
    @23
    vy
    cv
    #
    csp
    co
    #
    @7
    @25
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    #
    @24
    @9
    @4
    @28
    vy
    chil
    @9
    @4
    @25
    chil
    wcel
    #
    @28
    @9
    @4
    wa
    @30
    wa
    @5
    @25
    @3
    cfv
    #
    csp
    co
    #
    @5
    @25
    @1
    cfv
    #
    csp
    co
    #
    @26
    @27
    @4
    @32
    @34
    wceq
    @9
    @30
    @4
    @31
    @33
    @5
    csp
    @25
    @3
    @1
    fveq1
    oveq2d
    ad2antlr
    @9
    @30
    @26
    @32
    wceq
    @4
    @5
    @25
    cH
    cG
    pjco.2
    pjco.1
    pjadjcoi
    adantlr
    @9
    @30
    @27
    @34
    wceq
    @4
    @5
    @25
    cG
    pjco.1
    pjadji
    adantlr
    3eqtr4d
    exp31
    ralrimdv
    @9
    @23
    chil
    wcel
    @7
    chil
    wcel
    @29
    @24
    wb
    @5
    cH
    cG
    pjco.2
    pjco.1
    pjcohcli
    @5
    cG
    pjco.1
    pjhcli
    vy
    @23
    @7
    hial2eq
    syl2anc
    sylibd
    com12
    ralrimiv
    vx
    @21
    @1
    @2
    @1
    @20
    @19
    hocofi
    @19
    hoeqi
    sylib
    cG
    cH
    pjco.1
    pjco.2
    pjss1coi
    sylibr
    impbii
end
