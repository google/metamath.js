include "cz.mm"
include "wcel.mm"
include "cppi.mm"
include "cfv.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "cprime.mm"
include "cin.mm"
include "chash.mm"
include "c2.mm"
include "cfz.mm"
include "cr.mm"
include "wceq.mm"
include "zre.mm"
include "ppival.mm"
include "syl.mm"
include "cfl.mm"
include "ppisval.mm"
include "flid.mm"
include "oveq2d.mm"
include "ineq1d.mm"
include "eqtrd.mm"
include "fveq2d.mm"

theorem ppival2
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cB: class B
  let cP: class P


  assert |- ( A e. ZZ -> ( ppi ` A ) = ( # ` ( ( 2 ... A ) i^i Prime ) ) )

  proof
    cA
    cz
    wcel
    #
    cA
    cppi
    cfv
    #
    cc0
    cA
    cicc
    co
    cprime
    cin
    #
    chash
    cfv
    #
    c2
    cA
    cfz
    co
    #
    cprime
    cin
    #
    chash
    cfv
    @0
    cA
    cr
    wcel
    #
    @1
    @3
    wceq
    cA
    zre
    #
    cA
    ppival
    syl
    @0
    @2
    @5
    chash
    @0
    @2
    c2
    cA
    cfl
    cfv
    #
    cfz
    co
    #
    cprime
    cin
    #
    @5
    @0
    @6
    @2
    @10
    wceq
    @7
    cA
    ppisval
    syl
    @0
    @9
    @4
    cprime
    @0
    @8
    cA
    c2
    cfz
    cA
    flid
    oveq2d
    ineq1d
    eqtrd
    fveq2d
    eqtrd
end
