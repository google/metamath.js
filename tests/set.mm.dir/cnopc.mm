include "ccop.mm"
include "wcel.mm"
include "chil.mm"
include "crp.mm"
include "cv.mm"
include "cmv.mm"
include "co.mm"
include "cno.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "wf.mm"
include "elcnop.mm"
include "simprbi.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "imbi12d.mm"
include "rexralbidv.mm"
include "breq2.mm"
include "imbi2d.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "3impib.mm"

theorem cnopc
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cT: class T
  let vw: setvar w
  let vz: setvar z
  let cC: class C
  let cS: class S

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint T x
  disjoint T y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B w
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T z
  disjoint T w
  assert |- ( ( T e. ContOp /\ A e. ~H /\ B e. RR+ ) -> E. x e. RR+ A. y e. ~H ( ( normh ` ( y -h A ) ) < x -> ( normh ` ( ( T ` y ) -h ( T ` A ) ) ) < B ) )

  proof
    cT
    ccop
    wcel
    #
    cA
    chil
    wcel
    #
    cB
    crp
    wcel
    #
    vy
    cv
    #
    cA
    cmv
    co
    #
    cno
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    @3
    cT
    cfv
    #
    cA
    cT
    cfv
    #
    cmv
    co
    #
    cno
    cfv
    #
    cB
    clt
    wbr
    #
    wi
    #
    vy
    chil
    wral
    vx
    crp
    wrex
    #
    @0
    @3
    vz
    cv
    #
    cmv
    co
    #
    cno
    cfv
    #
    @6
    clt
    wbr
    #
    @8
    @15
    cT
    cfv
    #
    cmv
    co
    #
    cno
    cfv
    #
    vw
    cv
    #
    clt
    wbr
    #
    wi
    #
    vy
    chil
    wral
    vx
    crp
    wrex
    #
    vw
    crp
    wral
    vz
    chil
    wral
    #
    @1
    @2
    wa
    @14
    @0
    chil
    chil
    cT
    wf
    @26
    vz
    vw
    vx
    vy
    cT
    elcnop
    simprbi
    @25
    @14
    @7
    @11
    @22
    clt
    wbr
    #
    wi
    #
    vy
    chil
    wral
    vx
    crp
    wrex
    vz
    vw
    cA
    cB
    chil
    crp
    @15
    cA
    wceq
    #
    @24
    @28
    vx
    vy
    crp
    chil
    @29
    @18
    @7
    @23
    @27
    @29
    @17
    @5
    @6
    clt
    @29
    @16
    @4
    cno
    @15
    cA
    @3
    cmv
    oveq2
    fveq2d
    breq1d
    @29
    @21
    @11
    @22
    clt
    @29
    @20
    @10
    cno
    @29
    @19
    @9
    @8
    cmv
    @15
    cA
    cT
    fveq2
    oveq2d
    fveq2d
    breq1d
    imbi12d
    rexralbidv
    @22
    cB
    wceq
    #
    @28
    @13
    vx
    vy
    crp
    chil
    @30
    @27
    @12
    @7
    @22
    cB
    @11
    clt
    breq2
    imbi2d
    rexralbidv
    rspc2v
    syl5com
    3impib
end
