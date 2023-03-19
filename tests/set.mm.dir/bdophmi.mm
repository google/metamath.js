include "cc.mm"
include "wcel.mm"
include "chot.mm"
include "co.mm"
include "clo.mm"
include "cnop.mm"
include "cfv.mm"
include "cr.mm"
include "cbo.mm"
include "bdopln.mm"
include "ax-mp.mm"
include "lnopmi.mm"
include "cabs.mm"
include "cmul.mm"
include "nmophmi.mm"
include "abscl.mm"
include "nmopre.mm"
include "remulcl.mm"
include "sylancl.mm"
include "eqeltrd.mm"
include "elbdop2.mm"
include "sylanbrc.mm"

theorem bdophmi
  let cA: class A
  let cT: class T
  let vx: setvar x
  assume nmophm.1: |- T e. BndLinOp


  assert |- ( A e. CC -> ( A .op T ) e. BndLinOp )

  proof
    cA
    cc
    wcel
    #
    cA
    cT
    chot
    co
    #
    clo
    wcel
    @1
    cnop
    cfv
    #
    cr
    wcel
    @1
    cbo
    wcel
    cA
    cT
    cT
    cbo
    wcel
    #
    cT
    clo
    wcel
    nmophm.1
    cT
    bdopln
    ax-mp
    lnopmi
    @0
    @2
    cA
    cabs
    cfv
    #
    cT
    cnop
    cfv
    #
    cmul
    co
    #
    cr
    cA
    cT
    nmophm.1
    nmophmi
    @0
    @4
    cr
    wcel
    @5
    cr
    wcel
    #
    @6
    cr
    wcel
    cA
    abscl
    @3
    @7
    nmophm.1
    cT
    nmopre
    ax-mp
    @4
    @5
    remulcl
    sylancl
    eqeltrd
    @1
    elbdop2
    sylanbrc
end
