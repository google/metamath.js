include "wcel.mm"
include "cpsmet.mm"
include "cfv.mm"
include "cxr.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "wf.mm"
include "crab.mm"
include "cvv.mm"
include "elex.mm"
include "id.mm"
include "sqxpeqd.mm"
include "oveq2d.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "anbi2d.mm"
include "rabeqbidv.mm"
include "df-psmet.mm"
include "ovex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "syl.mm"
include "eleq2d.mm"
include "oveq.mm"
include "eqeq1d.mm"
include "oveq12d.mm"
include "breq12d.mm"
include "2ralbidv.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"
include "wb.mm"
include "xrex.mm"
include "sqxpexg.mm"
include "elmapg.mm"
include "sylancr.mm"
include "anbi1d.mm"
include "bitrd.mm"

theorem ispsmet
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cV: class V
  let cX: class X
  let vd: setvar d
  let vu: setvar u

  disjoint x y
  disjoint x z
  disjoint X x
  disjoint y z
  disjoint X y
  disjoint X z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint d u
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint X d
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint X u
  disjoint D d
  assert |- ( X e. V -> ( D e. ( PsMet ` X ) <-> ( D : ( X X. X ) --> RR* /\ A. x e. X ( ( x D x ) = 0 /\ A. y e. X A. z e. X ( x D y ) <_ ( ( z D x ) +e ( z D y ) ) ) ) ) )

  proof
    cX
    cV
    wcel
    #
    cD
    cX
    cpsmet
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
    @6
    cD
    co
    #
    cc0
    wceq
    #
    @6
    vy
    cv
    #
    cD
    co
    #
    vz
    cv
    #
    @6
    cD
    co
    #
    @11
    @9
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
    vy
    cX
    wral
    #
    wa
    #
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
    @18
    wa
    @0
    @2
    cD
    @6
    @6
    vd
    cv
    #
    co
    #
    cc0
    wceq
    #
    @6
    @9
    @21
    co
    #
    @11
    @6
    @21
    co
    #
    @11
    @9
    @21
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
    vy
    cX
    wral
    #
    wa
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
    @19
    @0
    @1
    @33
    cD
    @0
    cX
    cvv
    wcel
    @1
    @33
    wceq
    cX
    cV
    elex
    vu
    cX
    @23
    @28
    vz
    vu
    cv
    #
    wral
    #
    vy
    @34
    wral
    #
    wa
    #
    vx
    @34
    wral
    #
    vd
    cxr
    @34
    @34
    cxp
    #
    cmap
    co
    #
    crab
    @33
    cvv
    cpsmet
    @34
    cX
    wceq
    #
    @38
    @32
    vd
    @40
    @4
    @41
    @39
    @3
    cxr
    cmap
    @41
    @34
    cX
    @41
    id
    sqxpeqd
    oveq2d
    @37
    @31
    vx
    @34
    cX
    @41
    @36
    @30
    @23
    @35
    @29
    vy
    @34
    cX
    @28
    vz
    @34
    cX
    raleq
    raleqbi1dv
    anbi2d
    raleqbi1dv
    rabeqbidv
    vu
    vx
    vy
    vz
    vd
    df-psmet
    @32
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
    @32
    @18
    vd
    cD
    @4
    @21
    cD
    wceq
    #
    @31
    @17
    vx
    cX
    @42
    @23
    @8
    @30
    @16
    @42
    @22
    @7
    cc0
    @6
    @6
    @21
    cD
    oveq
    eqeq1d
    @42
    @28
    @15
    vy
    vz
    cX
    cX
    @42
    @24
    @10
    @27
    @14
    cle
    @6
    @9
    @21
    cD
    oveq
    @42
    @25
    @12
    @26
    @13
    cxad
    @11
    @6
    @21
    cD
    oveq
    @11
    @9
    @21
    cD
    oveq
    oveq12d
    breq12d
    2ralbidv
    anbi12d
    ralbidv
    elrab
    syl6bb
    @0
    @5
    @20
    @18
    @0
    cxr
    cvv
    wcel
    @3
    cvv
    wcel
    @5
    @20
    wb
    xrex
    cX
    cV
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
