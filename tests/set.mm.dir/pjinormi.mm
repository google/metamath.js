include "chil.mm"
include "wcel.mm"
include "cpjh.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "cno.mm"
include "c2.mm"
include "cexp.mm"
include "wceq.mm"
include "c0v.mm"
include "cif.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "ifhvhv0.mm"
include "pjinormii.mm"
include "dedth.mm"

theorem pjinormi
  let cA: class A
  let cH: class H
  assume pjadjt.1: |- H e. CH


  assert |- ( A e. ~H -> ( ( ( projh ` H ) ` A ) .ih A ) = ( ( normh ` ( ( projh ` H ) ` A ) ) ^ 2 ) )

  proof
    cA
    chil
    wcel
    #
    cA
    cH
    cpjh
    cfv
    #
    cfv
    #
    cA
    csp
    co
    #
    @2
    cno
    cfv
    #
    c2
    cexp
    co
    #
    wceq
    @0
    cA
    c0v
    cif
    #
    @1
    cfv
    #
    @6
    csp
    co
    #
    @7
    cno
    cfv
    #
    c2
    cexp
    co
    #
    wceq
    cA
    c0v
    cA
    @6
    wceq
    #
    @3
    @8
    @5
    @10
    @11
    @2
    @7
    cA
    @6
    csp
    cA
    @6
    @1
    fveq2
    #
    @11
    id
    oveq12d
    @11
    @4
    @9
    c2
    cexp
    @11
    @2
    @7
    cno
    @12
    fveq2d
    oveq1d
    eqeq12d
    @6
    cH
    pjadjt.1
    cA
    ifhvhv0
    pjinormii
    dedth
end
