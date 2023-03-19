include "chil.mm"
include "wf.mm"
include "cei.mm"
include "cfv.mm"
include "wcel.mm"
include "cel.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "cno.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "cmpt.mm"
include "eigvalfval.mm"
include "fveq1d.mm"
include "wceq.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem eigvalval
  let cA: class A
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( ( T : ~H --> ~H /\ A e. ( eigvec ` T ) ) -> ( ( eigval ` T ) ` A ) = ( ( ( T ` A ) .ih A ) / ( ( normh ` A ) ^ 2 ) ) )

  proof
    chil
    chil
    cT
    wf
    #
    cA
    cT
    cei
    cfv
    #
    wcel
    cA
    cT
    cel
    cfv
    #
    cfv
    cA
    vx
    @1
    vx
    cv
    #
    cT
    cfv
    #
    @3
    csp
    co
    #
    @3
    cno
    cfv
    #
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cmpt
    #
    cfv
    cA
    cT
    cfv
    #
    cA
    csp
    co
    #
    cA
    cno
    cfv
    #
    c2
    cexp
    co
    #
    cdiv
    co
    #
    @0
    cA
    @2
    @9
    vx
    cT
    eigvalfval
    fveq1d
    vx
    cA
    @8
    @14
    @1
    @9
    @3
    cA
    wceq
    #
    @5
    @11
    @7
    @13
    cdiv
    @15
    @4
    @10
    @3
    cA
    csp
    @3
    cA
    cT
    fveq2
    @15
    id
    oveq12d
    @15
    @6
    @12
    c2
    cexp
    @3
    cA
    cno
    fveq2
    oveq1d
    oveq12d
    @9
    eqid
    @11
    @13
    cdiv
    ovex
    fvmpt
    sylan9eq
end
