include "cdm.mm"
include "cima.mm"
include "crn.mm"
include "csh.mm"
include "imadmrn.mm"
include "chil.mm"
include "lnopfi.mm"
include "fdmi.mm"
include "helsh.mm"
include "eqeltri.mm"
include "imaelshi.mm"
include "eqeltrri.mm"

theorem rnelshi
  let cT: class T
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume rnelsh.1: |- T e. LinOp


  assert |- ran T e. SH

  proof
    cT
    cT
    cdm
    #
    cima
    cT
    crn
    csh
    cT
    imadmrn
    @0
    cT
    rnelsh.1
    @0
    chil
    csh
    chil
    chil
    cT
    cT
    rnelsh.1
    lnopfi
    fdmi
    helsh
    eqeltri
    imaelshi
    eqeltrri
end
