include "carea.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cr.mm"
include "areaf.mm"
include "ffvelrni.mm"
include "cle.mm"
include "wbr.mm"
include "elrege0.mm"
include "simplbi.mm"
include "syl.mm"

theorem areacl
  let cS: class S
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- ( S e. dom area -> ( area ` S ) e. RR )

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
    @1
    cr
    wcel
    #
    @0
    @2
    cS
    carea
    areaf
    ffvelrni
    @3
    @4
    cc0
    @1
    cle
    wbr
    @1
    elrege0
    simplbi
    syl
end
