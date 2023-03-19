include "chil.mm"
include "wcel.mm"
include "wss.mm"
include "cpjh.mm"
include "cfv.mm"
include "cmv.mm"
include "co.mm"
include "cort.mm"
include "cin.mm"
include "wceq.mm"
include "wi.mm"
include "c0v.mm"
include "cif.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "ifhvhv0.mm"
include "pjssmii.mm"
include "dedth.mm"

theorem pjssmi
  let cA: class A
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjco.1: |- G e. CH
  assume pjco.2: |- H e. CH


  assert |- ( A e. ~H -> ( H C_ G -> ( ( ( projh ` G ) ` A ) -h ( ( projh ` H ) ` A ) ) = ( ( projh ` ( G i^i ( _|_ ` H ) ) ) ` A ) ) )

  proof
    cA
    chil
    wcel
    #
    cH
    cG
    wss
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
    wi
    @1
    @0
    cA
    c0v
    cif
    #
    @2
    cfv
    #
    @10
    @4
    cfv
    #
    cmv
    co
    #
    @10
    @7
    cfv
    #
    wceq
    #
    wi
    cA
    c0v
    cA
    @10
    wceq
    #
    @9
    @15
    @1
    @16
    @6
    @13
    @8
    @14
    @16
    @3
    @11
    @5
    @12
    cmv
    cA
    @10
    @2
    fveq2
    cA
    @10
    @4
    fveq2
    oveq12d
    cA
    @10
    @7
    fveq2
    eqeq12d
    imbi2d
    @10
    cG
    cH
    pjco.2
    cA
    ifhvhv0
    pjco.1
    pjssmii
    dedth
end
