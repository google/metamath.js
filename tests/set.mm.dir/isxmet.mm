include "wcel.mm"
include "cxmt.mm"
include "cfv.mm"
include "cxr.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "wf.mm"
include "crab.mm"
include "cvv.mm"
include "elex.mm"
include "xpeq12.mm"
include "anidms.mm"
include "oveq2d.mm"
include "raleq.mm"
include "anbi2d.mm"
include "raleqbi1dv.mm"
include "rabeqbidv.mm"
include "df-xmet.mm"
include "ovex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "syl.mm"
include "eleq2d.mm"
include "oveq.mm"
include "eqeq1d.mm"
include "bibi1d.mm"
include "oveq12d.mm"
include "breq12d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "2ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"
include "xrex.mm"
include "sqxpexg.mm"
include "elmapg.mm"
include "sylancr.mm"
include "anbi1d.mm"
include "bitrd.mm"

theorem isxmet
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cD: class D
  let cX: class X
  let vd: setvar d
  let vt: setvar t

  disjoint x y
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint D d
  disjoint d t
  disjoint X d
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint X t
  assert |- ( X e. A -> ( D e. ( *Met ` X ) <-> ( D : ( X X. X ) --> RR* /\ A. x e. X A. y e. X ( ( ( x D y ) = 0 <-> x = y ) /\ A. z e. X ( x D y ) <_ ( ( z D x ) +e ( z D y ) ) ) ) ) )

  proof
    cX
    cA
    wcel
    #
    cD
    cX
    cxmt
    cfv
    #
    wcel
    #
    cD
    cxr
    cX
    cX
    cxp
    #
    cmap
    co
    #
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cD
    co
    #
    cc0
    wceq
    #
    @6
    @7
    wceq
    #
    wb
    #
    @8
    vz
    cv
    #
    @6
    cD
    co
    #
    @12
    @7
    cD
    co
    #
    cxad
    co
    #
    cle
    wbr
    #
    vz
    cX
    wral
    #
    wa
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    wa
    #
    @3
    cxr
    cD
    wf
    #
    @19
    wa
    @0
    @2
    cD
    @6
    @7
    vd
    cv
    #
    co
    #
    cc0
    wceq
    #
    @10
    wb
    #
    @23
    @12
    @6
    @22
    co
    #
    @12
    @7
    @22
    co
    #
    cxad
    co
    #
    cle
    wbr
    #
    vz
    cX
    wral
    #
    wa
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    vd
    @4
    crab
    #
    wcel
    @20
    @0
    @1
    @34
    cD
    @0
    cX
    cvv
    wcel
    @1
    @34
    wceq
    cX
    cA
    elex
    vt
    cX
    @25
    @29
    vz
    vt
    cv
    #
    wral
    #
    wa
    #
    vy
    @35
    wral
    #
    vx
    @35
    wral
    #
    vd
    cxr
    @35
    @35
    cxp
    #
    cmap
    co
    #
    crab
    @34
    cvv
    cxmt
    @35
    cX
    wceq
    #
    @39
    @33
    vd
    @41
    @4
    @42
    @40
    @3
    cxr
    cmap
    @42
    @40
    @3
    wceq
    @35
    cX
    @35
    cX
    xpeq12
    anidms
    oveq2d
    @38
    @32
    vx
    @35
    cX
    @37
    @31
    vy
    @35
    cX
    @42
    @36
    @30
    @25
    @29
    vz
    @35
    cX
    raleq
    anbi2d
    raleqbi1dv
    raleqbi1dv
    rabeqbidv
    vt
    vx
    vy
    vz
    vd
    df-xmet
    @33
    vd
    @4
    cxr
    @3
    cmap
    ovex
    rabex
    fvmpt
    syl
    eleq2d
    @33
    @19
    vd
    cD
    @4
    @22
    cD
    wceq
    #
    @31
    @18
    vx
    vy
    cX
    cX
    @43
    @25
    @11
    @30
    @17
    @43
    @24
    @9
    @10
    @43
    @23
    @8
    cc0
    @6
    @7
    @22
    cD
    oveq
    #
    eqeq1d
    bibi1d
    @43
    @29
    @16
    vz
    cX
    @43
    @23
    @8
    @28
    @15
    cle
    @44
    @43
    @26
    @13
    @27
    @14
    cxad
    @12
    @6
    @22
    cD
    oveq
    @12
    @7
    @22
    cD
    oveq
    oveq12d
    breq12d
    ralbidv
    anbi12d
    2ralbidv
    elrab
    syl6bb
    @0
    @5
    @21
    @19
    @0
    cxr
    cvv
    wcel
    @3
    cvv
    wcel
    @5
    @21
    wb
    xrex
    cX
    cA
    sqxpexg
    cxr
    @3
    cD
    cvv
    cvv
    elmapg
    sylancr
    anbi1d
    bitrd
end
