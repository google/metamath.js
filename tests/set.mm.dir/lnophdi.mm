include "c1.mm"
include "cneg.mm"
include "chot.mm"
include "co.mm"
include "chos.mm"
include "chod.mm"
include "clo.mm"
include "lnopfi.mm"
include "honegsubi.mm"
include "cc.mm"
include "wcel.mm"
include "neg1cn.mm"
include "lnopmi.mm"
include "ax-mp.mm"
include "lnophsi.mm"
include "eqeltrri.mm"

theorem lnophdi
  let cS: class S
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lnopco.1: |- S e. LinOp
  assume lnopco.2: |- T e. LinOp


  assert |- ( S -op T ) e. LinOp

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
    clo
    cS
    cT
    cS
    lnopco.1
    lnopfi
    cT
    lnopco.2
    lnopfi
    honegsubi
    cS
    @1
    lnopco.1
    @0
    cc
    wcel
    @1
    clo
    wcel
    neg1cn
    @0
    cT
    lnopco.2
    lnopmi
    ax-mp
    lnophsi
    eqeltrri
end
