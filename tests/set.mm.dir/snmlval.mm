include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "cn.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cmo.mm"
include "cfl.mm"
include "wceq.mm"
include "c1.mm"
include "cfz.mm"
include "crab.mm"
include "chash.mm"
include "cdiv.mm"
include "cmpt.mm"
include "cli.mm"
include "wbr.mm"
include "cc0.mm"
include "cmin.mm"
include "wral.mm"
include "w3a.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "id.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "rabbidv.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "oveq2.mm"
include "breq12d.mm"
include "raleqbidv.mm"
include "reex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "eleq2d.mm"
include "breq1d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"
include "pm5.32i.mm"
include "cdm.mm"
include "dmmptss.mm"
include "elfvdm.mm"
include "sseldi.mm"
include "pm4.71ri.mm"
include "3anass.mm"
include "3bitr4i.mm"

theorem snmlval
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vb: setvar b
  let cB: class B
  let cF: class F
  assume snml.s: |- S = ( r e. ( ZZ>= ` 2 ) |-> { x e. RR | A. b e. ( 0 ... ( r - 1 ) ) ( n e. NN |-> ( ( # ` { k e. ( 1 ... n ) | ( |_ ` ( ( x x. ( r ^ k ) ) mod r ) ) = b } ) / n ) ) ~~> ( 1 / r ) } )

  disjoint b k
  disjoint b n
  disjoint b x
  disjoint A b
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint b r
  disjoint R b
  disjoint k r
  disjoint R k
  disjoint n r
  disjoint R n
  disjoint r x
  disjoint R r
  disjoint R x
  disjoint B b
  disjoint B k
  disjoint B n
  disjoint F b
  assert |- ( A e. ( S ` R ) <-> ( R e. ( ZZ>= ` 2 ) /\ A e. RR /\ A. b e. ( 0 ... ( R - 1 ) ) ( n e. NN |-> ( ( # ` { k e. ( 1 ... n ) | ( |_ ` ( ( A x. ( R ^ k ) ) mod R ) ) = b } ) / n ) ) ~~> ( 1 / R ) ) )

  proof
    cR
    c2
    cuz
    cfv
    #
    wcel
    #
    cA
    cR
    cS
    cfv
    #
    wcel
    #
    wa
    @1
    cA
    cr
    wcel
    #
    vn
    cn
    cA
    cR
    vk
    cv
    #
    cexp
    co
    #
    cmul
    co
    #
    cR
    cmo
    co
    #
    cfl
    cfv
    #
    vb
    cv
    #
    wceq
    #
    vk
    c1
    vn
    cv
    #
    cfz
    co
    #
    crab
    #
    chash
    cfv
    #
    @12
    cdiv
    co
    #
    cmpt
    #
    c1
    cR
    cdiv
    co
    #
    cli
    wbr
    #
    vb
    cc0
    cR
    c1
    cmin
    co
    #
    cfz
    co
    #
    wral
    #
    wa
    #
    wa
    @3
    @1
    @4
    @22
    w3a
    @1
    @3
    @23
    @1
    @3
    cA
    vn
    cn
    vx
    cv
    #
    @6
    cmul
    co
    #
    cR
    cmo
    co
    #
    cfl
    cfv
    #
    @10
    wceq
    #
    vk
    @13
    crab
    #
    chash
    cfv
    #
    @12
    cdiv
    co
    #
    cmpt
    #
    @18
    cli
    wbr
    #
    vb
    @21
    wral
    #
    vx
    cr
    crab
    #
    wcel
    @23
    @1
    @2
    @35
    cA
    vr
    cR
    vn
    cn
    @24
    vr
    cv
    #
    @5
    cexp
    co
    #
    cmul
    co
    #
    @36
    cmo
    co
    #
    cfl
    cfv
    #
    @10
    wceq
    #
    vk
    @13
    crab
    #
    chash
    cfv
    #
    @12
    cdiv
    co
    #
    cmpt
    #
    c1
    @36
    cdiv
    co
    #
    cli
    wbr
    #
    vb
    cc0
    @36
    c1
    cmin
    co
    #
    cfz
    co
    #
    wral
    #
    vx
    cr
    crab
    #
    @35
    @0
    cS
    @36
    cR
    wceq
    #
    @50
    @34
    vx
    cr
    @52
    @47
    @33
    vb
    @49
    @21
    @52
    @48
    @20
    cc0
    cfz
    @36
    cR
    c1
    cmin
    oveq1
    oveq2d
    @52
    @45
    @32
    @46
    @18
    cli
    @52
    vn
    cn
    @44
    @31
    @52
    @43
    @30
    @12
    cdiv
    @52
    @42
    @29
    chash
    @52
    @41
    @28
    vk
    @13
    @52
    @40
    @27
    @10
    @52
    @39
    @26
    cfl
    @52
    @38
    @25
    @36
    cR
    cmo
    @52
    @37
    @6
    @24
    cmul
    @36
    cR
    @5
    cexp
    oveq1
    oveq2d
    @52
    id
    oveq12d
    fveq2d
    eqeq1d
    rabbidv
    fveq2d
    oveq1d
    mpteq2dv
    @36
    cR
    c1
    cdiv
    oveq2
    breq12d
    raleqbidv
    rabbidv
    snml.s
    @34
    vx
    cr
    reex
    rabex
    fvmpt
    eleq2d
    @34
    @22
    vx
    cA
    cr
    @24
    cA
    wceq
    #
    @33
    @19
    vb
    @21
    @53
    @32
    @17
    @18
    cli
    @53
    vn
    cn
    @31
    @16
    @53
    @30
    @15
    @12
    cdiv
    @53
    @29
    @14
    chash
    @53
    @28
    @11
    vk
    @13
    @53
    @27
    @9
    @10
    @53
    @26
    @8
    cfl
    @53
    @25
    @7
    cR
    cmo
    @24
    cA
    @6
    cmul
    oveq1
    oveq1d
    fveq2d
    eqeq1d
    rabbidv
    fveq2d
    oveq1d
    mpteq2dv
    breq1d
    ralbidv
    elrab
    syl6bb
    pm5.32i
    @3
    @1
    @3
    cS
    cdm
    @0
    cR
    vr
    @0
    @51
    cS
    snml.s
    dmmptss
    cA
    cR
    cS
    elfvdm
    sseldi
    pm4.71ri
    @1
    @4
    @22
    3anass
    3bitr4i
end
