include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "cppi.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "cprime.mm"
include "cin.mm"
include "chash.mm"
include "cfz.mm"
include "cr.mm"
include "wceq.mm"
include "zre.mm"
include "adantr.mm"
include "ppival.mm"
include "syl.mm"
include "cfl.mm"
include "ppisval2.mm"
include "sylan.mm"
include "flid.mm"
include "oveq2d.mm"
include "ineq1d.mm"
include "eqtrd.mm"
include "fveq2d.mm"

theorem ppival2g
  let cA: class A
  let cM: class M
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cN: class N
  let cS: class S
  let cB: class B
  let cP: class P


  assert |- ( ( A e. ZZ /\ 2 e. ( ZZ>= ` M ) ) -> ( ppi ` A ) = ( # ` ( ( M ... A ) i^i Prime ) ) )

  proof
    cA
    cz
    wcel
    #
    c2
    cM
    cuz
    cfv
    wcel
    #
    wa
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
    cM
    cA
    cfz
    co
    #
    cprime
    cin
    #
    chash
    cfv
    @2
    cA
    cr
    wcel
    #
    @3
    @5
    wceq
    @0
    @8
    @1
    cA
    zre
    #
    adantr
    cA
    ppival
    syl
    @2
    @4
    @7
    chash
    @2
    @4
    cM
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
    @7
    @0
    @8
    @1
    @4
    @12
    wceq
    @9
    cA
    cM
    ppisval2
    sylan
    @0
    @12
    @7
    wceq
    @1
    @0
    @11
    @6
    cprime
    @0
    @10
    cA
    cM
    cfz
    cA
    flid
    oveq2d
    ineq1d
    adantr
    eqtrd
    fveq2d
    eqtrd
end
