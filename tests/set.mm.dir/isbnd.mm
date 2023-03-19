include "cbnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cvv.mm"
include "cme.mm"
include "cv.mm"
include "cbl.mm"
include "co.mm"
include "wceq.mm"
include "crp.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "elfvex.mm"
include "adantr.mm"
include "crab.mm"
include "fveq2.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "raleqbi1dv.mm"
include "rabeqbidv.mm"
include "df-bnd.mm"
include "fvex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "eleq2d.mm"
include "oveqd.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"
include "pm5.21nii.mm"

theorem isbnd
  let vx: setvar x
  let cM: class M
  let cX: class X
  let vr: setvar r
  let vd: setvar d
  let vm: setvar m
  let vs: setvar s
  let vy: setvar y
  let vz: setvar z
  let cN: class N
  let cP: class P
  let cR: class R
  let cS: class S
  let cY: class Y

  disjoint r x
  disjoint M r
  disjoint M x
  disjoint X r
  disjoint X x
  disjoint d m
  disjoint d r
  disjoint d s
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint M d
  disjoint m r
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint M m
  disjoint r s
  disjoint r y
  disjoint r z
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint M s
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint M y
  disjoint M z
  disjoint N d
  disjoint N r
  disjoint N y
  disjoint P d
  disjoint P r
  disjoint P y
  disjoint X d
  disjoint X m
  disjoint X s
  disjoint X y
  disjoint X z
  disjoint R r
  disjoint R x
  disjoint S r
  disjoint S x
  disjoint Y d
  disjoint Y r
  disjoint Y x
  disjoint Y y
  assert |- ( M e. ( Bnd ` X ) <-> ( M e. ( Met ` X ) /\ A. x e. X E. r e. RR+ X = ( x ( ball ` M ) r ) ) )

  proof
    cM
    cX
    cbnd
    cfv
    #
    wcel
    #
    cX
    cvv
    wcel
    #
    cM
    cX
    cme
    cfv
    #
    wcel
    #
    cX
    vx
    cv
    #
    vr
    cv
    #
    cM
    cbl
    cfv
    #
    co
    #
    wceq
    #
    vr
    crp
    wrex
    #
    vx
    cX
    wral
    #
    wa
    #
    cM
    cX
    cbnd
    elfvex
    @4
    @2
    @11
    cM
    cX
    cme
    elfvex
    adantr
    @2
    @1
    cM
    cX
    @5
    @6
    vm
    cv
    #
    cbl
    cfv
    #
    co
    #
    wceq
    #
    vr
    crp
    wrex
    #
    vx
    cX
    wral
    #
    vm
    @3
    crab
    #
    wcel
    @12
    @2
    @0
    @19
    cM
    vy
    cX
    vy
    cv
    #
    @15
    wceq
    #
    vr
    crp
    wrex
    #
    vx
    @20
    wral
    #
    vm
    @20
    cme
    cfv
    #
    crab
    @19
    cvv
    cbnd
    @20
    cX
    wceq
    #
    @23
    @18
    vm
    @24
    @3
    @20
    cX
    cme
    fveq2
    @22
    @17
    vx
    @20
    cX
    @25
    @21
    @16
    vr
    crp
    @20
    cX
    @15
    eqeq1
    rexbidv
    raleqbi1dv
    rabeqbidv
    vy
    vx
    vm
    vr
    df-bnd
    @18
    vm
    @3
    cX
    cme
    fvex
    rabex
    fvmpt
    eleq2d
    @18
    @11
    vm
    cM
    @3
    @13
    cM
    wceq
    #
    @17
    @10
    vx
    cX
    @26
    @16
    @9
    vr
    crp
    @26
    @15
    @8
    cX
    @26
    @14
    @7
    @5
    @6
    @13
    cM
    cbl
    fveq2
    oveqd
    eqeq2d
    rexbidv
    ralbidv
    elrab
    syl6bb
    pm5.21nii
end
