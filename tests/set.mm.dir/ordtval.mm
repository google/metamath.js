include "wcel.mm"
include "cvv.mm"
include "cordt.mm"
include "cfv.mm"
include "csn.mm"
include "cun.mm"
include "cfi.mm"
include "ctg.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "cdm.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "dmeq.mm"
include "syl6eqr.mm"
include "sneqd.mm"
include "rnun.mm"
include "breq.mm"
include "notbid.mm"
include "rabeqbidv.mm"
include "mpteq12dv.mm"
include "rneqd.mm"
include "uneq12d.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "df-ordt.mm"
include "fvex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem ordtval
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  let cC: class C
  assume ordtval.1: |- X = dom R
  assume ordtval.2: |- A = ran ( x e. X |-> { y e. X | -. y R x } )
  assume ordtval.3: |- B = ran ( x e. X |-> { y e. X | -. x R y } )

  disjoint x y
  disjoint R x
  disjoint R y
  disjoint X x
  disjoint X y
  disjoint V x
  disjoint a b
  disjoint a m
  disjoint a n
  disjoint a r
  disjoint a w
  disjoint a z
  disjoint A a
  disjoint b m
  disjoint b n
  disjoint b r
  disjoint b w
  disjoint b z
  disjoint A b
  disjoint m n
  disjoint m r
  disjoint m w
  disjoint m z
  disjoint A m
  disjoint n r
  disjoint n w
  disjoint n z
  disjoint A n
  disjoint r w
  disjoint r z
  disjoint A r
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint a x
  disjoint a y
  disjoint R a
  disjoint b x
  disjoint b y
  disjoint R b
  disjoint m x
  disjoint m y
  disjoint R m
  disjoint n x
  disjoint n y
  disjoint R n
  disjoint r x
  disjoint r y
  disjoint R r
  disjoint w x
  disjoint w y
  disjoint R w
  disjoint x z
  disjoint y z
  disjoint R z
  disjoint X a
  disjoint X b
  disjoint X m
  disjoint X n
  disjoint X r
  disjoint X w
  disjoint X z
  disjoint B a
  disjoint B b
  disjoint B m
  disjoint B n
  disjoint B r
  disjoint B z
  disjoint C m
  disjoint C n
  disjoint C z
  assert |- ( R e. V -> ( ordTop ` R ) = ( topGen ` ( fi ` ( { X } u. ( A u. B ) ) ) ) )

  proof
    cR
    cV
    wcel
    cR
    cvv
    wcel
    cR
    cordt
    cfv
    cX
    csn
    #
    cA
    cB
    cun
    #
    cun
    #
    cfi
    cfv
    #
    ctg
    cfv
    #
    wceq
    cR
    cV
    elex
    vr
    cR
    vr
    cv
    #
    cdm
    #
    csn
    #
    vx
    @6
    vy
    cv
    #
    vx
    cv
    #
    @5
    wbr
    #
    wn
    #
    vy
    @6
    crab
    #
    cmpt
    #
    vx
    @6
    @9
    @8
    @5
    wbr
    #
    wn
    #
    vy
    @6
    crab
    #
    cmpt
    #
    cun
    crn
    #
    cun
    #
    cfi
    cfv
    #
    ctg
    cfv
    @4
    cvv
    cordt
    @5
    cR
    wceq
    #
    @20
    @3
    ctg
    @21
    @19
    @2
    cfi
    @21
    @7
    @0
    @18
    @1
    @21
    @6
    cX
    @21
    @6
    cR
    cdm
    cX
    @5
    cR
    dmeq
    ordtval.1
    syl6eqr
    #
    sneqd
    @21
    @18
    @13
    crn
    #
    @17
    crn
    #
    cun
    @1
    @13
    @17
    rnun
    @21
    @23
    cA
    @24
    cB
    @21
    @23
    vx
    cX
    @8
    @9
    cR
    wbr
    #
    wn
    #
    vy
    cX
    crab
    #
    cmpt
    #
    crn
    cA
    @21
    @13
    @28
    @21
    vx
    @6
    @12
    cX
    @27
    @22
    @21
    @11
    @26
    vy
    @6
    cX
    @22
    @21
    @10
    @25
    @8
    @9
    @5
    cR
    breq
    notbid
    rabeqbidv
    mpteq12dv
    rneqd
    ordtval.2
    syl6eqr
    @21
    @24
    vx
    cX
    @9
    @8
    cR
    wbr
    #
    wn
    #
    vy
    cX
    crab
    #
    cmpt
    #
    crn
    cB
    @21
    @17
    @32
    @21
    vx
    @6
    @16
    cX
    @31
    @22
    @21
    @15
    @30
    vy
    @6
    cX
    @22
    @21
    @14
    @29
    @9
    @8
    @5
    cR
    breq
    notbid
    rabeqbidv
    mpteq12dv
    rneqd
    ordtval.3
    syl6eqr
    uneq12d
    syl5eq
    uneq12d
    fveq2d
    fveq2d
    vx
    vy
    vr
    df-ordt
    @3
    ctg
    fvex
    fvmpt
    syl
end
