include "cuo.mm"
include "wcel.mm"
include "chil.mm"
include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "csp.mm"
include "co.mm"
include "elunop.mm"
include "simplbi.mm"
include "fof.mm"
include "syl.mm"
include "wa.mm"
include "cmv.mm"
include "cc0.mm"
include "caddc.mm"
include "cmin.mm"
include "w3a.mm"
include "unop.mm"
include "3anidm23.mm"
include "3adant3.mm"
include "3adant2.mm"
include "oveq12d.mm"
include "3com23.mm"
include "3expb.mm"
include "ffvelrn.mm"
include "anim12dan.mm"
include "sylan.mm"
include "normlem9at.mm"
include "adantl.mm"
include "3eqtr4rd.mm"
include "eqeq1d.mm"
include "wb.mm"
include "c0v.mm"
include "hvsubcl.mm"
include "his6.mm"
include "hvsubeq0.mm"
include "bitrd.mm"
include "3bitr3rd.mm"
include "biimpd.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "df-f1o.mm"

theorem unopf1o
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( T e. UniOp -> T : ~H -1-1-onto-> ~H )

  proof
    cT
    cuo
    wcel
    #
    chil
    chil
    cT
    wf1
    #
    chil
    chil
    cT
    wfo
    #
    chil
    chil
    cT
    wf1o
    @0
    chil
    chil
    cT
    wf
    #
    vx
    cv
    #
    cT
    cfv
    #
    vy
    cv
    #
    cT
    cfv
    #
    wceq
    #
    @4
    @6
    wceq
    #
    wi
    #
    vy
    chil
    wral
    vx
    chil
    wral
    @1
    @0
    @2
    @3
    @0
    @2
    @5
    @7
    csp
    co
    #
    @4
    @6
    csp
    co
    #
    wceq
    vy
    chil
    wral
    vx
    chil
    wral
    vx
    vy
    cT
    elunop
    simplbi
    #
    chil
    chil
    cT
    fof
    syl
    #
    @0
    @10
    vx
    vy
    chil
    chil
    @0
    @4
    chil
    wcel
    #
    @6
    chil
    wcel
    #
    wa
    #
    wa
    #
    @8
    @9
    @18
    @4
    @6
    cmv
    co
    #
    @19
    csp
    co
    #
    cc0
    wceq
    #
    @5
    @7
    cmv
    co
    #
    @22
    csp
    co
    #
    cc0
    wceq
    #
    @9
    @8
    @18
    @20
    @23
    cc0
    @18
    @5
    @5
    csp
    co
    #
    @7
    @7
    csp
    co
    #
    caddc
    co
    #
    @11
    @7
    @5
    csp
    co
    #
    caddc
    co
    #
    cmin
    co
    #
    @4
    @4
    csp
    co
    #
    @6
    @6
    csp
    co
    #
    caddc
    co
    #
    @12
    @6
    @4
    csp
    co
    #
    caddc
    co
    #
    cmin
    co
    #
    @23
    @20
    @0
    @15
    @16
    @30
    @36
    wceq
    @0
    @15
    @16
    w3a
    #
    @27
    @33
    @29
    @35
    cmin
    @37
    @25
    @31
    @26
    @32
    caddc
    @0
    @15
    @25
    @31
    wceq
    #
    @16
    @0
    @15
    @38
    @4
    @4
    cT
    unop
    3anidm23
    3adant3
    @0
    @16
    @26
    @32
    wceq
    #
    @15
    @0
    @16
    @39
    @6
    @6
    cT
    unop
    3anidm23
    3adant2
    oveq12d
    @37
    @11
    @12
    @28
    @34
    caddc
    @4
    @6
    cT
    unop
    @0
    @16
    @15
    @28
    @34
    wceq
    @6
    @4
    cT
    unop
    3com23
    oveq12d
    oveq12d
    3expb
    @18
    @5
    chil
    wcel
    #
    @7
    chil
    wcel
    #
    wa
    #
    @23
    @30
    wceq
    @0
    @3
    @17
    @42
    @14
    @3
    @15
    @40
    @16
    @41
    chil
    chil
    @4
    cT
    ffvelrn
    chil
    chil
    @6
    cT
    ffvelrn
    anim12dan
    sylan
    #
    @5
    @7
    normlem9at
    syl
    @17
    @20
    @36
    wceq
    @0
    @4
    @6
    normlem9at
    adantl
    3eqtr4rd
    eqeq1d
    @17
    @21
    @9
    wb
    @0
    @17
    @21
    @19
    c0v
    wceq
    #
    @9
    @17
    @19
    chil
    wcel
    @21
    @44
    wb
    @4
    @6
    hvsubcl
    @19
    his6
    syl
    @4
    @6
    hvsubeq0
    bitrd
    adantl
    @18
    @42
    @24
    @8
    wb
    @43
    @42
    @24
    @22
    c0v
    wceq
    #
    @8
    @42
    @22
    chil
    wcel
    @24
    @45
    wb
    @5
    @7
    hvsubcl
    @22
    his6
    syl
    @5
    @7
    hvsubeq0
    bitrd
    syl
    3bitr3rd
    biimpd
    ralrimivva
    vx
    vy
    chil
    chil
    cT
    dff13
    sylanbrc
    @13
    chil
    chil
    cT
    df-f1o
    sylanbrc
end
