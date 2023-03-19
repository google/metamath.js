include "chil.mm"
include "wf.mm"
include "cei.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cel.mm"
include "csm.mm"
include "co.mm"
include "wceq.mm"
include "c0v.mm"
include "wne.mm"
include "csp.mm"
include "cno.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "eigvalval.mm"
include "oveq1d.mm"
include "csn.mm"
include "cspn.mm"
include "w3a.mm"
include "eleigvec2.mm"
include "biimpa.mm"
include "normcan.mm"
include "syl.mm"
include "eqtr2d.mm"
include "simp2d.mm"
include "jca.mm"

theorem eigvec1
  let cA: class A
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( ( T : ~H --> ~H /\ A e. ( eigvec ` T ) ) -> ( ( T ` A ) = ( ( ( eigval ` T ) ` A ) .h A ) /\ A =/= 0h ) )

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
    wcel
    #
    wa
    #
    cA
    cT
    cfv
    #
    cA
    cT
    cel
    cfv
    cfv
    #
    cA
    csm
    co
    #
    wceq
    cA
    c0v
    wne
    #
    @2
    @5
    @3
    cA
    csp
    co
    cA
    cno
    cfv
    c2
    cexp
    co
    cdiv
    co
    #
    cA
    csm
    co
    #
    @3
    @2
    @4
    @7
    cA
    csm
    cA
    cT
    eigvalval
    oveq1d
    @2
    cA
    chil
    wcel
    #
    @6
    @3
    cA
    csn
    cspn
    cfv
    wcel
    #
    w3a
    #
    @8
    @3
    wceq
    @0
    @1
    @11
    cA
    cT
    eleigvec2
    biimpa
    #
    @3
    cA
    normcan
    syl
    eqtr2d
    @2
    @9
    @6
    @10
    @12
    simp2d
    jca
end
