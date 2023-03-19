include "carea.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "areaf.mm"
include "ffvelrni.mm"
include "cr.mm"
include "elrege0.mm"
include "simprbi.mm"
include "syl.mm"

theorem areage0
  let cS: class S
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- ( S e. dom area -> 0 <_ ( area ` S ) )

  proof
    cS
    carea
    cdm
    #
    wcel
    cS
    carea
    cfv
    #
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    cc0
    @1
    cle
    wbr
    #
    @0
    @2
    cS
    carea
    areaf
    ffvelrni
    @3
    @1
    cr
    wcel
    @4
    @1
    elrege0
    simprbi
    syl
end
