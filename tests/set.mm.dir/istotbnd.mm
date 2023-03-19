include "ctotbnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cvv.mm"
include "cme.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "cbl.mm"
include "co.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "cfn.mm"
include "crp.mm"
include "elfvex.mm"
include "adantr.mm"
include "crab.mm"
include "fveq2.mm"
include "eqeq2.mm"
include "rexeq.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "rabeqbidv.mm"
include "df-totbnd.mm"
include "fvex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "eleq2d.mm"
include "oveqd.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "elrab.mm"
include "syl6bb.mm"
include "pm5.21nii.mm"

theorem istotbnd
  let vx: setvar x
  let vv: setvar v
  let cM: class M
  let cX: class X
  let vb: setvar b
  let vd: setvar d
  let vm: setvar m
  let vy: setvar y

  disjoint b d
  disjoint b v
  disjoint b x
  disjoint M b
  disjoint d v
  disjoint d x
  disjoint M d
  disjoint v x
  disjoint M v
  disjoint M x
  disjoint X b
  disjoint X d
  disjoint X v
  disjoint X x
  disjoint b m
  disjoint d m
  disjoint m v
  disjoint m x
  disjoint M m
  disjoint b y
  disjoint d y
  disjoint m y
  disjoint X m
  disjoint v y
  disjoint x y
  disjoint X y
  assert |- ( M e. ( TotBnd ` X ) <-> ( M e. ( Met ` X ) /\ A. d e. RR+ E. v e. Fin ( U. v = X /\ A. b e. v E. x e. X b = ( x ( ball ` M ) d ) ) ) )

  proof
    cM
    cX
    ctotbnd
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
    vv
    cv
    #
    cuni
    #
    cX
    wceq
    #
    vb
    cv
    #
    vx
    cv
    #
    vd
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
    vx
    cX
    wrex
    #
    vb
    @5
    wral
    #
    wa
    #
    vv
    cfn
    wrex
    #
    vd
    crp
    wral
    #
    wa
    #
    cM
    cX
    ctotbnd
    elfvex
    @4
    @2
    @18
    cM
    cX
    cme
    elfvex
    adantr
    @2
    @1
    cM
    @7
    @8
    @9
    @10
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
    vx
    cX
    wrex
    #
    vb
    @5
    wral
    #
    wa
    #
    vv
    cfn
    wrex
    #
    vd
    crp
    wral
    #
    vm
    @3
    crab
    #
    wcel
    @19
    @2
    @0
    @29
    cM
    vy
    cX
    @6
    vy
    cv
    #
    wceq
    #
    @23
    vx
    @30
    wrex
    #
    vb
    @5
    wral
    #
    wa
    #
    vv
    cfn
    wrex
    #
    vd
    crp
    wral
    #
    vm
    @30
    cme
    cfv
    #
    crab
    @29
    cvv
    ctotbnd
    @30
    cX
    wceq
    #
    @36
    @28
    vm
    @37
    @3
    @30
    cX
    cme
    fveq2
    @38
    @35
    @27
    vd
    crp
    @38
    @34
    @26
    vv
    cfn
    @38
    @31
    @7
    @33
    @25
    @30
    cX
    @6
    eqeq2
    @38
    @32
    @24
    vb
    @5
    @23
    vx
    @30
    cX
    rexeq
    ralbidv
    anbi12d
    rexbidv
    ralbidv
    rabeqbidv
    vy
    vx
    vv
    vm
    vb
    vd
    df-totbnd
    @28
    vm
    @3
    cX
    cme
    fvex
    rabex
    fvmpt
    eleq2d
    @28
    @18
    vm
    cM
    @3
    @20
    cM
    wceq
    #
    @27
    @17
    vd
    crp
    @39
    @26
    @16
    vv
    cfn
    @39
    @25
    @15
    @7
    @39
    @24
    @14
    vb
    @5
    @39
    @23
    @13
    vx
    cX
    @39
    @22
    @12
    @8
    @39
    @21
    @11
    @9
    @10
    @20
    cM
    cbl
    fveq2
    oveqd
    eqeq2d
    rexbidv
    ralbidv
    anbi2d
    rexbidv
    ralbidv
    elrab
    syl6bb
    pm5.21nii
end
