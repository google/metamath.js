include "cc0.mm"
include "cv.mm"
include "cicc.mm"
include "co.mm"
include "cprime.mm"
include "cin.mm"
include "chash.mm"
include "cfv.mm"
include "cr.mm"
include "cppi.mm"
include "wceq.mm"
include "oveq2.mm"
include "ineq1d.mm"
include "fveq2d.mm"
include "df-ppi.mm"
include "fvex.mm"
include "fvmpt.mm"

theorem ppival
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


  assert |- ( A e. RR -> ( ppi ` A ) = ( # ` ( ( 0 [,] A ) i^i Prime ) ) )

  proof
    vx
    cA
    cc0
    vx
    cv
    #
    cicc
    co
    #
    cprime
    cin
    #
    chash
    cfv
    cc0
    cA
    cicc
    co
    #
    cprime
    cin
    #
    chash
    cfv
    cr
    cppi
    @0
    cA
    wceq
    #
    @2
    @4
    chash
    @5
    @1
    @3
    cprime
    @0
    cA
    cc0
    cicc
    oveq2
    ineq1d
    fveq2d
    vx
    df-ppi
    @4
    chash
    fvex
    fvmpt
end
