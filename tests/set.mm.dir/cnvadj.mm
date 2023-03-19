include "chil.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "copab.mm"
include "ccnv.mm"
include "cado.mm"
include "cnvopab.mm"
include "3ancoma.mm"
include "wa.mm"
include "wcel.mm"
include "wb.mm"
include "ccj.mm"
include "ffvelrn.mm"
include "ax-his1.mm"
include "sylan.mm"
include "adantrl.mm"
include "sylan2.mm"
include "adantll.mm"
include "eqeq12d.mm"
include "ancoms.mm"
include "cc.mm"
include "hicl.mm"
include "cj11.mm"
include "syl2anc.mm"
include "bitr2d.mm"
include "an4s.mm"
include "anassrs.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "ralbidva.mm"
include "ralcom.mm"
include "pm5.32i.mm"
include "df-3an.mm"
include "3bitr4i.mm"
include "bitri.mm"
include "opabbii.mm"
include "eqtri.mm"
include "dfadj2.mm"
include "cnveqi.mm"
include "3eqtr4i.mm"

theorem cnvadj
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cT: class T


  assert |- `' adjh = adjh

  proof
    chil
    chil
    vu
    cv
    #
    wf
    #
    chil
    chil
    vt
    cv
    #
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    @0
    cfv
    #
    csp
    co
    #
    @4
    @2
    cfv
    #
    @5
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    #
    vx
    chil
    wral
    #
    w3a
    #
    vu
    vt
    copab
    #
    ccnv
    #
    @3
    @1
    @5
    @8
    csp
    co
    #
    @6
    @4
    csp
    co
    #
    wceq
    #
    vx
    chil
    wral
    vy
    chil
    wral
    #
    w3a
    #
    vt
    vu
    copab
    #
    cado
    ccnv
    cado
    @15
    @13
    vt
    vu
    copab
    @21
    @13
    vu
    vt
    cnvopab
    @13
    @20
    vt
    vu
    @13
    @3
    @1
    @12
    w3a
    #
    @20
    @1
    @3
    @12
    3ancoma
    @3
    @1
    wa
    #
    @12
    wa
    @23
    @19
    wa
    @22
    @20
    @23
    @12
    @19
    @23
    @12
    @18
    vy
    chil
    wral
    #
    vx
    chil
    wral
    @19
    @23
    @11
    @24
    vx
    chil
    @23
    @4
    chil
    wcel
    #
    wa
    #
    @10
    @18
    vy
    chil
    @26
    @5
    chil
    wcel
    #
    wa
    @10
    @17
    @16
    wceq
    #
    @18
    @23
    @25
    @27
    @10
    @28
    wb
    #
    @3
    @25
    @1
    @27
    @29
    @3
    @25
    wa
    #
    @1
    @27
    wa
    #
    wa
    #
    @28
    @7
    ccj
    cfv
    #
    @9
    ccj
    cfv
    #
    wceq
    #
    @10
    @31
    @30
    @28
    @35
    wb
    @31
    @30
    wa
    @17
    @33
    @16
    @34
    @31
    @25
    @17
    @33
    wceq
    #
    @3
    @31
    @6
    chil
    wcel
    #
    @25
    @36
    chil
    chil
    @5
    @0
    ffvelrn
    #
    @6
    @4
    ax-his1
    sylan
    adantrl
    @27
    @30
    @16
    @34
    wceq
    #
    @1
    @30
    @27
    @8
    chil
    wcel
    #
    @39
    chil
    chil
    @4
    @2
    ffvelrn
    #
    @5
    @8
    ax-his1
    sylan2
    adantll
    eqeq12d
    ancoms
    @32
    @7
    cc
    wcel
    #
    @9
    cc
    wcel
    #
    @35
    @10
    wb
    @25
    @31
    @42
    @3
    @31
    @25
    @37
    @42
    @38
    @4
    @6
    hicl
    sylan2
    adantll
    @30
    @27
    @43
    @1
    @30
    @40
    @27
    @43
    @41
    @8
    @5
    hicl
    sylan
    adantrl
    @7
    @9
    cj11
    syl2anc
    bitr2d
    an4s
    anassrs
    @17
    @16
    eqcom
    syl6bb
    ralbidva
    ralbidva
    @18
    vx
    vy
    chil
    chil
    ralcom
    syl6bb
    pm5.32i
    @3
    @1
    @12
    df-3an
    @3
    @1
    @19
    df-3an
    3bitr4i
    bitri
    opabbii
    eqtri
    cado
    @14
    vx
    vy
    vt
    vu
    dfadj2
    cnveqi
    vy
    vx
    vu
    vt
    dfadj2
    3eqtr4i
end
