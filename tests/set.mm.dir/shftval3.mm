include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cshi.mm"
include "cfv.mm"
include "wceq.mm"
include "0cn.mm"
include "shftval2.mm"
include "mp3an3.mm"
include "addid1.mm"
include "adantr.mm"
include "fveq2d.mm"
include "adantl.mm"
include "3eqtr3d.mm"

theorem shftval3
  let cA: class A
  let cB: class B
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume shftfval.1: |- F e. _V


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( F shift ( A - B ) ) ` A ) = ( F ` B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cc0
    caddc
    co
    #
    cF
    cA
    cB
    cmin
    co
    cshi
    co
    #
    cfv
    #
    cB
    cc0
    caddc
    co
    #
    cF
    cfv
    #
    cA
    @4
    cfv
    cB
    cF
    cfv
    @0
    @1
    cc0
    cc
    wcel
    @5
    @7
    wceq
    0cn
    cA
    cB
    cc0
    cF
    shftfval.1
    shftval2
    mp3an3
    @2
    @3
    cA
    @4
    @0
    @3
    cA
    wceq
    @1
    cA
    addid1
    adantr
    fveq2d
    @2
    @6
    cB
    cF
    @1
    @6
    cB
    wceq
    @0
    cB
    addid1
    adantl
    fveq2d
    3eqtr3d
end
