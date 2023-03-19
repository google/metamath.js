include "cho.mm"
include "wcel.mm"
include "cado.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cdm.mm"
include "chil.mm"
include "wf.mm"
include "wn.mm"
include "hmopf.mm"
include "hon0.mm"
include "syl.mm"
include "hmopadj.mm"
include "eqeq1d.mm"
include "mtbird.mm"
include "ndmfv.mm"
include "nsyl2.mm"

theorem hmdmadj
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( T e. HrmOp -> T e. dom adjh )

  proof
    cT
    cho
    wcel
    #
    cT
    cado
    cfv
    #
    c0
    wceq
    #
    cT
    cado
    cdm
    wcel
    @0
    @2
    cT
    c0
    wceq
    #
    @0
    chil
    chil
    cT
    wf
    @3
    wn
    cT
    hmopf
    cT
    hon0
    syl
    @0
    @1
    cT
    c0
    cT
    hmopadj
    eqeq1d
    mtbird
    cT
    cado
    ndmfv
    nsyl2
end
