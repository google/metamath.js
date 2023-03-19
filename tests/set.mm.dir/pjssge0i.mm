include "chil.mm"
include "wcel.mm"
include "cpjh.mm"
include "cfv.mm"
include "cmv.mm"
include "co.mm"
include "cort.mm"
include "cin.mm"
include "wceq.mm"
include "cc0.mm"
include "csp.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "c0v.mm"
include "cif.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "id.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "ifhvhv0.mm"
include "pjssge0ii.mm"
include "dedth.mm"

theorem pjssge0i
  let cA: class A
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjco.1: |- G e. CH
  assume pjco.2: |- H e. CH


  assert |- ( A e. ~H -> ( ( ( ( projh ` G ) ` A ) -h ( ( projh ` H ) ` A ) ) = ( ( projh ` ( G i^i ( _|_ ` H ) ) ) ` A ) -> 0 <_ ( ( ( ( projh ` G ) ` A ) -h ( ( projh ` H ) ` A ) ) .ih A ) ) )

  proof
    cA
    chil
    wcel
    #
    cA
    cG
    cpjh
    cfv
    #
    cfv
    #
    cA
    cH
    cpjh
    cfv
    #
    cfv
    #
    cmv
    co
    #
    cA
    cG
    cH
    cort
    cfv
    cin
    cpjh
    cfv
    #
    cfv
    #
    wceq
    #
    cc0
    @5
    cA
    csp
    co
    #
    cle
    wbr
    #
    wi
    @0
    cA
    c0v
    cif
    #
    @1
    cfv
    #
    @11
    @3
    cfv
    #
    cmv
    co
    #
    @11
    @6
    cfv
    #
    wceq
    #
    cc0
    @14
    @11
    csp
    co
    #
    cle
    wbr
    #
    wi
    cA
    c0v
    cA
    @11
    wceq
    #
    @8
    @16
    @10
    @18
    @19
    @5
    @14
    @7
    @15
    @19
    @2
    @12
    @4
    @13
    cmv
    cA
    @11
    @1
    fveq2
    cA
    @11
    @3
    fveq2
    oveq12d
    #
    cA
    @11
    @6
    fveq2
    eqeq12d
    @19
    @9
    @17
    cc0
    cle
    @19
    @5
    @14
    cA
    @11
    csp
    @20
    @19
    id
    oveq12d
    breq2d
    imbi12d
    @11
    cG
    cH
    pjco.2
    cA
    ifhvhv0
    pjco.1
    pjssge0ii
    dedth
end
