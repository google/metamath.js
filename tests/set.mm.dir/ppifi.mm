include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "cprime.mm"
include "cin.mm"
include "c2.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "cfn.mm"
include "ppisval.mm"
include "wss.mm"
include "fzfi.mm"
include "inss1.mm"
include "ssfi.mm"
include "mp2an.mm"
include "syl6eqel.mm"

theorem ppifi
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


  assert |- ( A e. RR -> ( ( 0 [,] A ) i^i Prime ) e. Fin )

  proof
    cA
    cr
    wcel
    cc0
    cA
    cicc
    co
    cprime
    cin
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
    cfn
    cA
    ppisval
    @1
    cfn
    wcel
    @2
    @1
    wss
    @2
    cfn
    wcel
    c2
    @0
    fzfi
    @1
    cprime
    inss1
    @1
    @2
    ssfi
    mp2an
    syl6eqel
end
