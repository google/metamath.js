include "cr.mm"
include "cn0.mm"
include "cc0.mm"
include "cv.mm"
include "cicc.mm"
include "co.mm"
include "cprime.mm"
include "cin.mm"
include "chash.mm"
include "cfv.mm"
include "cppi.mm"
include "df-ppi.mm"
include "wcel.mm"
include "cfn.mm"
include "ppifi.mm"
include "hashcl.mm"
include "syl.mm"
include "fmpti.mm"

theorem ppif
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cB: class B
  let cP: class P


  assert |- ppi : RR --> NN0

  proof
    vx
    cr
    cn0
    cc0
    vx
    cv
    #
    cicc
    co
    cprime
    cin
    #
    chash
    cfv
    #
    cppi
    vx
    df-ppi
    @0
    cr
    wcel
    @1
    cfn
    wcel
    @2
    cn0
    wcel
    @0
    ppifi
    @1
    hashcl
    syl
    fmpti
end
