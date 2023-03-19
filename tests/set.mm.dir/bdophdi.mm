include "c1.mm"
include "cneg.mm"
include "chot.mm"
include "co.mm"
include "chos.mm"
include "chod.mm"
include "cbo.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "bdopf.mm"
include "ax-mp.mm"
include "honegsubi.mm"
include "cc.mm"
include "neg1cn.mm"
include "bdophmi.mm"
include "bdophsi.mm"
include "eqeltrri.mm"

theorem bdophdi
  let cS: class S
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  assume nmoptri.1: |- S e. BndLinOp
  assume nmoptri.2: |- T e. BndLinOp


  assert |- ( S -op T ) e. BndLinOp

  proof
    cS
    c1
    cneg
    #
    cT
    chot
    co
    #
    chos
    co
    cS
    cT
    chod
    co
    cbo
    cS
    cT
    cS
    cbo
    wcel
    chil
    chil
    cS
    wf
    nmoptri.1
    cS
    bdopf
    ax-mp
    cT
    cbo
    wcel
    chil
    chil
    cT
    wf
    nmoptri.2
    cT
    bdopf
    ax-mp
    honegsubi
    cS
    @1
    nmoptri.1
    @0
    cc
    wcel
    @1
    cbo
    wcel
    neg1cn
    @0
    cT
    nmoptri.2
    bdophmi
    ax-mp
    bdophsi
    eqeltrri
end
