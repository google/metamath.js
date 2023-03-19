include "chlt.mm"
include "wcel.mm"
include "coml.mm"
include "ccla.mm"
include "cin.mm"
include "clc.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "w3a.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "cjn.mm"
include "cfv.mm"
include "cple.mm"
include "catm.mm"
include "cp0.mm"
include "cplt.mm"
include "cp1.mm"
include "cbs.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "breqd.mm"
include "oveqd.mm"
include "breq2d.mm"
include "bitrd.mm"
include "3anbi3d.mm"
include "rexeqbidv.mm"
include "imbi2d.mm"
include "raleqbidv.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "df-hlat.mm"
include "elrab2.mm"
include "elin.mm"
include "anbi1i.mm"
include "df-3an.mm"
include "3bitr4ri.mm"
include "bitr4i.mm"

theorem ishlat1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let c.lt: class .<
  let c.1: class .1.
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.0: class .0.
  let vk: setvar k
  assume ishlat.b: |- B = ( Base ` K )
  assume ishlat.l: |- .<_ = ( le ` K )
  assume ishlat.s: |- .< = ( lt ` K )
  assume ishlat.j: |- .\/ = ( join ` K )
  assume ishlat.z: |- .0. = ( 0. ` K )
  assume ishlat.u: |- .1. = ( 1. ` K )
  assume ishlat.a: |- A = ( Atoms ` K )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint B k
  disjoint .\/ k
  disjoint K k
  disjoint .<_ k
  disjoint .< k
  disjoint .1. k
  disjoint .0. k
  assert |- ( K e. HL <-> ( ( K e. OML /\ K e. CLat /\ K e. CvLat ) /\ ( A. x e. A A. y e. A ( x =/= y -> E. z e. A ( z =/= x /\ z =/= y /\ z .<_ ( x .\/ y ) ) ) /\ E. x e. B E. y e. B E. z e. B ( ( .0. .< x /\ x .< y ) /\ ( y .< z /\ z .< .1. ) ) ) ) )

  proof
    cK
    chlt
    wcel
    cK
    coml
    ccla
    cin
    #
    clc
    cin
    #
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    vz
    cv
    #
    @3
    wne
    #
    @6
    @4
    wne
    #
    @6
    @3
    @4
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    #
    vz
    cA
    wrex
    #
    wi
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    c.0
    @3
    c.lt
    wbr
    #
    @3
    @4
    c.lt
    wbr
    #
    wa
    #
    @4
    @6
    c.lt
    wbr
    #
    @6
    c.1
    c.lt
    wbr
    #
    wa
    #
    wa
    #
    vz
    cB
    wrex
    #
    vy
    cB
    wrex
    #
    vx
    cB
    wrex
    #
    wa
    #
    wa
    cK
    coml
    wcel
    #
    cK
    ccla
    wcel
    #
    cK
    clc
    wcel
    #
    w3a
    #
    @26
    wa
    @5
    @7
    @8
    @6
    @3
    @4
    vk
    cv
    #
    cjn
    cfv
    #
    co
    #
    @31
    cple
    cfv
    #
    wbr
    #
    w3a
    #
    vz
    @31
    catm
    cfv
    #
    wrex
    #
    wi
    #
    vy
    @37
    wral
    #
    vx
    @37
    wral
    #
    @31
    cp0
    cfv
    #
    @3
    @31
    cplt
    cfv
    #
    wbr
    #
    @3
    @4
    @43
    wbr
    #
    wa
    #
    @4
    @6
    @43
    wbr
    #
    @6
    @31
    cp1
    cfv
    #
    @43
    wbr
    #
    wa
    #
    wa
    #
    vz
    @31
    cbs
    cfv
    #
    wrex
    #
    vy
    @52
    wrex
    #
    vx
    @52
    wrex
    #
    wa
    @26
    vk
    cK
    @1
    chlt
    @31
    cK
    wceq
    #
    @41
    @15
    @55
    @25
    @56
    @40
    @14
    vx
    @37
    cA
    @56
    @37
    cK
    catm
    cfv
    cA
    @31
    cK
    catm
    fveq2
    ishlat.a
    syl6eqr
    #
    @56
    @39
    @13
    vy
    @37
    cA
    @57
    @56
    @38
    @12
    @5
    @56
    @36
    @11
    vz
    @37
    cA
    @57
    @56
    @35
    @10
    @7
    @8
    @56
    @35
    @6
    @33
    c.le
    wbr
    @10
    @56
    @34
    c.le
    @6
    @33
    @56
    @34
    cK
    cple
    cfv
    c.le
    @31
    cK
    cple
    fveq2
    ishlat.l
    syl6eqr
    breqd
    @56
    @33
    @9
    @6
    c.le
    @56
    @32
    c.or
    @3
    @4
    @56
    @32
    cK
    cjn
    cfv
    c.or
    @31
    cK
    cjn
    fveq2
    ishlat.j
    syl6eqr
    oveqd
    breq2d
    bitrd
    3anbi3d
    rexeqbidv
    imbi2d
    raleqbidv
    raleqbidv
    @56
    @54
    @24
    vx
    @52
    cB
    @56
    @52
    cK
    cbs
    cfv
    cB
    @31
    cK
    cbs
    fveq2
    ishlat.b
    syl6eqr
    #
    @56
    @53
    @23
    vy
    @52
    cB
    @58
    @56
    @51
    @22
    vz
    @52
    cB
    @58
    @56
    @46
    @18
    @50
    @21
    @56
    @44
    @16
    @45
    @17
    @56
    @44
    @42
    @3
    c.lt
    wbr
    @16
    @56
    @43
    c.lt
    @42
    @3
    @56
    @43
    cK
    cplt
    cfv
    c.lt
    @31
    cK
    cplt
    fveq2
    ishlat.s
    syl6eqr
    #
    breqd
    @56
    @42
    c.0
    @3
    c.lt
    @56
    @42
    cK
    cp0
    cfv
    c.0
    @31
    cK
    cp0
    fveq2
    ishlat.z
    syl6eqr
    breq1d
    bitrd
    @56
    @43
    c.lt
    @3
    @4
    @59
    breqd
    anbi12d
    @56
    @47
    @19
    @49
    @20
    @56
    @43
    c.lt
    @4
    @6
    @59
    breqd
    @56
    @49
    @6
    @48
    c.lt
    wbr
    @20
    @56
    @43
    c.lt
    @6
    @48
    @59
    breqd
    @56
    @48
    c.1
    @6
    c.lt
    @56
    @48
    cK
    cp1
    cfv
    c.1
    @31
    cK
    cp1
    fveq2
    ishlat.u
    syl6eqr
    breq2d
    bitrd
    anbi12d
    anbi12d
    rexeqbidv
    rexeqbidv
    rexeqbidv
    anbi12d
    vx
    vy
    vz
    vk
    df-hlat
    elrab2
    @30
    @2
    @26
    cK
    @0
    wcel
    #
    @29
    wa
    @27
    @28
    wa
    #
    @29
    wa
    @2
    @30
    @60
    @61
    @29
    cK
    coml
    ccla
    elin
    anbi1i
    cK
    @0
    clc
    elin
    @27
    @28
    @29
    df-3an
    3bitr4ri
    anbi1i
    bitr4i
end
