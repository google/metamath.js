include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "w3a.mm"
include "csm.mm"
include "co.mm"
include "ck.mm"
include "cv.mm"
include "csp.mm"
include "cmpt.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "hvmulcl.mm"
include "kbfval.mm"
include "stoic3.mm"
include "simp2.mm"
include "cjcl.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "syl2anc.mm"
include "wa.mm"
include "cmul.mm"
include "simpr.mm"
include "simpl3.mm"
include "hicl.mm"
include "simpl1.mm"
include "simpl2.mm"
include "ax-hvmulass.mm"
include "syl3anc.mm"
include "mulcomd.mm"
include "his52.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "mpteq2dva.mm"

theorem kbmul
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cS: class S
  let cT: class T


  assert |- ( ( A e. CC /\ B e. ~H /\ C e. ~H ) -> ( ( A .h B ) ketbra C ) = ( B ketbra ( ( * ` A ) .h C ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    chil
    wcel
    #
    cC
    chil
    wcel
    #
    w3a
    #
    cA
    cB
    csm
    co
    #
    cC
    ck
    co
    #
    vx
    chil
    vx
    cv
    #
    cC
    csp
    co
    #
    @4
    csm
    co
    #
    cmpt
    #
    cB
    cA
    ccj
    cfv
    #
    cC
    csm
    co
    #
    ck
    co
    #
    @0
    @1
    @4
    chil
    wcel
    @2
    @5
    @9
    wceq
    cA
    cB
    hvmulcl
    vx
    @4
    cC
    kbfval
    stoic3
    @3
    @12
    vx
    chil
    @6
    @11
    csp
    co
    #
    cB
    csm
    co
    #
    cmpt
    #
    @9
    @3
    @1
    @11
    chil
    wcel
    #
    @12
    @15
    wceq
    @0
    @1
    @2
    simp2
    @3
    @10
    cc
    wcel
    #
    @2
    @16
    @0
    @1
    @17
    @2
    cA
    cjcl
    3ad2ant1
    @0
    @1
    @2
    simp3
    @10
    cC
    hvmulcl
    syl2anc
    vx
    cB
    @11
    kbfval
    syl2anc
    @3
    vx
    chil
    @8
    @14
    @3
    @6
    chil
    wcel
    #
    wa
    #
    @7
    cA
    cmul
    co
    #
    cB
    csm
    co
    #
    @8
    @14
    @19
    @7
    cc
    wcel
    #
    @0
    @1
    @21
    @8
    wceq
    @19
    @18
    @2
    @22
    @3
    @18
    simpr
    #
    @0
    @1
    @2
    @18
    simpl3
    #
    @6
    cC
    hicl
    syl2anc
    #
    @0
    @1
    @2
    @18
    simpl1
    #
    @0
    @1
    @2
    @18
    simpl2
    @7
    cA
    cB
    ax-hvmulass
    syl3anc
    @19
    @20
    @13
    cB
    csm
    @19
    @20
    cA
    @7
    cmul
    co
    #
    @13
    @19
    @7
    cA
    @25
    @26
    mulcomd
    @19
    @0
    @18
    @2
    @13
    @27
    wceq
    @26
    @23
    @24
    cA
    @6
    cC
    his52
    syl3anc
    eqtr4d
    oveq1d
    eqtr3d
    mpteq2dva
    eqtr4d
    eqtr4d
end
