include "cho.mm"
include "wcel.mm"
include "wa.mm"
include "cleo.mm"
include "wbr.mm"
include "cc0.mm"
include "cv.mm"
include "chod.mm"
include "co.mm"
include "cfv.mm"
include "csp.mm"
include "cle.mm"
include "chil.mm"
include "wral.mm"
include "leop.mm"
include "cmin.mm"
include "wf.mm"
include "wceq.mm"
include "hmopf.mm"
include "anim12i.mm"
include "cmv.mm"
include "hodval.mm"
include "3com12.mm"
include "3expa.mm"
include "oveq1d.mm"
include "ffvelrn.mm"
include "adantll.mm"
include "adantlr.mm"
include "simpr.mm"
include "his2sub.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "sylan.mm"
include "breq2d.mm"
include "cr.mm"
include "hmopre.mm"
include "subge0d.mm"
include "bitrd.mm"
include "ralbidva.mm"

theorem leop2
  let vx: setvar x
  let cT: class T
  let cU: class U
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vt: setvar t
  let vu: setvar u

  disjoint T x
  disjoint U x
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint S x
  disjoint t u
  disjoint t x
  disjoint t y
  disjoint T t
  disjoint u x
  disjoint u y
  disjoint T u
  disjoint T y
  disjoint U t
  disjoint U u
  disjoint t z
  assert |- ( ( T e. HrmOp /\ U e. HrmOp ) -> ( T <_op U <-> A. x e. ~H ( ( T ` x ) .ih x ) <_ ( ( U ` x ) .ih x ) ) )

  proof
    cT
    cho
    wcel
    #
    cU
    cho
    wcel
    #
    wa
    #
    cT
    cU
    cleo
    wbr
    cc0
    vx
    cv
    #
    cU
    cT
    chod
    co
    cfv
    #
    @3
    csp
    co
    #
    cle
    wbr
    #
    vx
    chil
    wral
    @3
    cT
    cfv
    #
    @3
    csp
    co
    #
    @3
    cU
    cfv
    #
    @3
    csp
    co
    #
    cle
    wbr
    #
    vx
    chil
    wral
    vx
    cT
    cU
    leop
    @2
    @6
    @11
    vx
    chil
    @2
    @3
    chil
    wcel
    #
    wa
    #
    @6
    cc0
    @10
    @8
    cmin
    co
    #
    cle
    wbr
    @11
    @13
    @5
    @14
    cc0
    cle
    @2
    chil
    chil
    cT
    wf
    #
    chil
    chil
    cU
    wf
    #
    wa
    #
    @12
    @5
    @14
    wceq
    @0
    @15
    @1
    @16
    cT
    hmopf
    cU
    hmopf
    anim12i
    @17
    @12
    wa
    #
    @5
    @9
    @7
    cmv
    co
    #
    @3
    csp
    co
    #
    @14
    @18
    @4
    @19
    @3
    csp
    @15
    @16
    @12
    @4
    @19
    wceq
    #
    @16
    @15
    @12
    @21
    @3
    cU
    cT
    hodval
    3com12
    3expa
    oveq1d
    @18
    @9
    chil
    wcel
    #
    @7
    chil
    wcel
    #
    @12
    @20
    @14
    wceq
    @16
    @12
    @22
    @15
    chil
    chil
    @3
    cU
    ffvelrn
    adantll
    @15
    @12
    @23
    @16
    chil
    chil
    @3
    cT
    ffvelrn
    adantlr
    @17
    @12
    simpr
    @9
    @7
    @3
    his2sub
    syl3anc
    eqtrd
    sylan
    breq2d
    @13
    @10
    @8
    @1
    @12
    @10
    cr
    wcel
    @0
    @3
    cU
    hmopre
    adantll
    @0
    @12
    @8
    cr
    wcel
    @1
    @3
    cT
    hmopre
    adantlr
    subge0d
    bitrd
    ralbidva
    bitrd
end
