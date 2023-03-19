include "cch.mm"
include "wss.mm"
include "chil.mm"
include "cpw.mm"
include "chsup.mm"
include "cfv.mm"
include "wcel.mm"
include "chsspwh.mm"
include "sstr2.mm"
include "mpi.mm"
include "hsupcl.mm"
include "syl.mm"

theorem chsupcl
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A C_ CH -> ( \/H ` A ) e. CH )

  proof
    cA
    cch
    wss
    #
    cA
    chil
    cpw
    #
    wss
    #
    cA
    chsup
    cfv
    cch
    wcel
    @0
    cch
    @1
    wss
    @2
    chsspwh
    cA
    cch
    @1
    sstr2
    mpi
    cA
    hsupcl
    syl
end
