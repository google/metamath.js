include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "ck.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "csp.mm"
include "csm.mm"
include "cmpt.mm"
include "cc.mm"
include "hicl.mm"
include "hvmulcl.mm"
include "sylan.mm"
include "an31s.mm"
include "eqid.mm"
include "fmptd.mm"
include "kbfval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem kbop
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cS: class S
  let cT: class T


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( A ketbra B ) : ~H --> ~H )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    #
    chil
    chil
    cA
    cB
    ck
    co
    #
    wf
    chil
    chil
    vx
    chil
    vx
    cv
    #
    cB
    csp
    co
    #
    cA
    csm
    co
    #
    cmpt
    #
    wf
    @2
    vx
    chil
    @6
    chil
    @7
    @4
    chil
    wcel
    #
    @1
    @0
    @6
    chil
    wcel
    #
    @8
    @1
    wa
    @5
    cc
    wcel
    @0
    @9
    @4
    cB
    hicl
    @5
    cA
    hvmulcl
    sylan
    an31s
    @7
    eqid
    fmptd
    @2
    chil
    chil
    @3
    @7
    vx
    cA
    cB
    kbfval
    feq1d
    mpbird
end
