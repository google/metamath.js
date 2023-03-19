include "wrel.mm"
include "cdm.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "cmpt.mm"
include "crn.mm"
include "wcel.mm"
include "wceq.mm"
include "wrex.mm"
include "releldm2.mm"
include "wfn.mm"
include "wb.mm"
include "fvex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "fvelrnb.mm"
include "ax-mp.mm"
include "fveq2.mm"
include "fvmpt.mm"
include "eqeq1d.mm"
include "rexbiia.mm"
include "a1i.mm"
include "syl5rbb.mm"
include "bitrd.mm"
include "eqrdv.mm"

theorem reldm
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( Rel A -> dom A = ran ( x e. A |-> ( 1st ` x ) ) )

  proof
    cA
    wrel
    #
    vy
    cA
    cdm
    #
    vx
    cA
    vx
    cv
    #
    c1st
    cfv
    #
    cmpt
    #
    crn
    #
    @0
    vy
    cv
    #
    @1
    wcel
    vz
    cv
    #
    c1st
    cfv
    #
    @6
    wceq
    #
    vz
    cA
    wrex
    #
    @6
    @5
    wcel
    #
    vz
    cA
    @6
    releldm2
    @11
    @7
    @4
    cfv
    #
    @6
    wceq
    #
    vz
    cA
    wrex
    #
    @0
    @10
    @4
    cA
    wfn
    @11
    @14
    wb
    vx
    cA
    @3
    @4
    @2
    c1st
    fvex
    @4
    eqid
    #
    fnmpti
    vz
    cA
    @6
    @4
    fvelrnb
    ax-mp
    @14
    @10
    wb
    @0
    @13
    @9
    vz
    cA
    @7
    cA
    wcel
    @12
    @8
    @6
    vx
    @7
    @3
    @8
    cA
    @4
    @2
    @7
    c1st
    fveq2
    @15
    @7
    c1st
    fvex
    fvmpt
    eqeq1d
    rexbiia
    a1i
    syl5rbb
    bitrd
    eqrdv
end
