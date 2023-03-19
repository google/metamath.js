include "chil.mm"
include "cv.mm"
include "cfv.mm"
include "cmv.mm"
include "co.mm"
include "chod.mm"
include "wf.mm"
include "cmpt.mm"
include "wceq.mm"
include "hodmval.mm"
include "mp2an.mm"
include "wcel.mm"
include "ffvelrni.mm"
include "hvsubcl.mm"
include "syl2anc.mm"
include "fmpti.mm"

theorem hosubcli
  let cS: class S
  let cT: class T
  let vx: setvar x
  assume hoeq.1: |- S : ~H --> ~H
  assume hoeq.2: |- T : ~H --> ~H


  assert |- ( S -op T ) : ~H --> ~H

  proof
    vx
    chil
    chil
    vx
    cv
    #
    cS
    cfv
    #
    @0
    cT
    cfv
    #
    cmv
    co
    #
    cS
    cT
    chod
    co
    #
    chil
    chil
    cS
    wf
    chil
    chil
    cT
    wf
    @4
    vx
    chil
    @3
    cmpt
    wceq
    hoeq.1
    hoeq.2
    vx
    cS
    cT
    hodmval
    mp2an
    @0
    chil
    wcel
    @1
    chil
    wcel
    @2
    chil
    wcel
    @3
    chil
    wcel
    chil
    chil
    @0
    cS
    hoeq.1
    ffvelrni
    chil
    chil
    @0
    cT
    hoeq.2
    ffvelrni
    @1
    @2
    hvsubcl
    syl2anc
    fmpti
end
