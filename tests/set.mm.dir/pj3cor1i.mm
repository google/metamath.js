include "cpjh.mm"
include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "chil.mm"
include "wral.mm"
include "wcel.mm"
include "csp.mm"
include "co.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "adantl.mm"
include "ad2antlr.mm"
include "cin.mm"
include "chincli.mm"
include "pjadji.mm"
include "adantlr.mm"
include "pj3i.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "pjadj2coi.mm"
include "exp31.mm"
include "ralrimdv.mm"
include "wb.mm"
include "pjfi.mm"
include "hocofi.mm"
include "hococli.mm"
include "hial2eq.mm"
include "syl2anc.mm"
include "sylibd.mm"
include "com12.mm"
include "ralrimiv.mm"
include "hoeqi.mm"
include "sylib.mm"

theorem pj3cor1i
  let cF: class F
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjadj2co.1: |- F e. CH
  assume pjadj2co.2: |- G e. CH
  assume pjadj2co.3: |- H e. CH


  assert |- ( ( ( ( ( projh ` F ) o. ( projh ` G ) ) o. ( projh ` H ) ) = ( ( ( projh ` H ) o. ( projh ` G ) ) o. ( projh ` F ) ) /\ ( ( ( projh ` F ) o. ( projh ` G ) ) o. ( projh ` H ) ) = ( ( ( projh ` G ) o. ( projh ` F ) ) o. ( projh ` H ) ) ) -> ( ( ( projh ` F ) o. ( projh ` G ) ) o. ( projh ` H ) ) = ( ( ( projh ` H ) o. ( projh ` F ) ) o. ( projh ` G ) ) )

  proof
    cF
    cpjh
    cfv
    #
    cG
    cpjh
    cfv
    #
    ccom
    #
    cH
    cpjh
    cfv
    #
    ccom
    #
    @3
    @1
    ccom
    @0
    ccom
    wceq
    #
    @4
    @1
    @0
    ccom
    @3
    ccom
    #
    wceq
    #
    wa
    #
    vx
    cv
    #
    @4
    cfv
    #
    @9
    @3
    @0
    ccom
    #
    @1
    ccom
    #
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    @4
    @12
    wceq
    @8
    @14
    vx
    chil
    @9
    chil
    wcel
    #
    @8
    @14
    @15
    @8
    @10
    vy
    cv
    #
    csp
    co
    #
    @13
    @16
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    #
    @14
    @15
    @8
    @19
    vy
    chil
    @15
    @8
    @16
    chil
    wcel
    #
    @19
    @15
    @8
    wa
    @21
    wa
    #
    @9
    @16
    @4
    cfv
    #
    csp
    co
    #
    @9
    @16
    @6
    cfv
    #
    csp
    co
    #
    @17
    @18
    @8
    @24
    @26
    wceq
    #
    @15
    @21
    @7
    @27
    @5
    @7
    @23
    @25
    @9
    csp
    @16
    @4
    @6
    fveq1
    oveq2d
    adantl
    ad2antlr
    @22
    @9
    cF
    cG
    cin
    #
    cH
    cin
    #
    cpjh
    cfv
    #
    cfv
    #
    @16
    csp
    co
    #
    @9
    @16
    @30
    cfv
    #
    csp
    co
    #
    @17
    @24
    @15
    @21
    @32
    @34
    wceq
    @8
    @9
    @16
    @29
    @28
    cH
    cF
    cG
    pjadj2co.1
    pjadj2co.2
    chincli
    pjadj2co.3
    chincli
    pjadji
    adantlr
    @8
    @17
    @32
    wceq
    @15
    @21
    @8
    @10
    @31
    @16
    csp
    @8
    @9
    @4
    @30
    cF
    cG
    cH
    pjadj2co.1
    pjadj2co.2
    pjadj2co.3
    pj3i
    #
    fveq1d
    oveq1d
    ad2antlr
    @8
    @24
    @34
    wceq
    @15
    @21
    @8
    @23
    @33
    @9
    csp
    @8
    @16
    @4
    @30
    @35
    fveq1d
    oveq2d
    ad2antlr
    3eqtr4d
    @15
    @21
    @18
    @26
    wceq
    @8
    @9
    @16
    cH
    cF
    cG
    pjadj2co.3
    pjadj2co.1
    pjadj2co.2
    pjadj2coi
    adantlr
    3eqtr4d
    exp31
    ralrimdv
    @15
    @10
    chil
    wcel
    @13
    chil
    wcel
    @20
    @14
    wb
    @9
    @2
    @3
    @0
    @1
    cF
    pjadj2co.1
    pjfi
    #
    cG
    pjadj2co.2
    pjfi
    #
    hocofi
    #
    cH
    pjadj2co.3
    pjfi
    #
    hococli
    @9
    @11
    @1
    @3
    @0
    @39
    @36
    hocofi
    #
    @37
    hococli
    vy
    @10
    @13
    hial2eq
    syl2anc
    sylibd
    com12
    ralrimiv
    vx
    @4
    @12
    @2
    @3
    @38
    @39
    hocofi
    @11
    @1
    @40
    @37
    hocofi
    hoeqi
    sylib
end
