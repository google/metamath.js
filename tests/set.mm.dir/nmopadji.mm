include "cado.mm"
include "cfv.mm"
include "cnop.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "nmopadjlem.mm"
include "cdm.mm"
include "wcel.mm"
include "cbo.mm"
include "bdopadj.mm"
include "ax-mp.mm"
include "adjadj.mm"
include "fveq2i.mm"
include "adjbdln.mm"
include "eqbrtrri.mm"
include "cr.mm"
include "nmopre.mm"
include "letri3i.mm"
include "mpbir2an.mm"

theorem nmopadji
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let vy: setvar y
  assume nmopadjle.1: |- T e. BndLinOp


  assert |- ( normop ` ( adjh ` T ) ) = ( normop ` T )

  proof
    cT
    cado
    cfv
    #
    cnop
    cfv
    #
    cT
    cnop
    cfv
    #
    wceq
    @1
    @2
    cle
    wbr
    @2
    @1
    cle
    wbr
    cT
    nmopadjle.1
    nmopadjlem
    @0
    cado
    cfv
    #
    cnop
    cfv
    @2
    @1
    cle
    @3
    cT
    cnop
    cT
    cado
    cdm
    wcel
    #
    @3
    cT
    wceq
    cT
    cbo
    wcel
    #
    @4
    nmopadjle.1
    cT
    bdopadj
    ax-mp
    cT
    adjadj
    ax-mp
    fveq2i
    @0
    @5
    @0
    cbo
    wcel
    #
    nmopadjle.1
    cT
    adjbdln
    ax-mp
    #
    nmopadjlem
    eqbrtrri
    @1
    @2
    @6
    @1
    cr
    wcel
    @7
    @0
    nmopre
    ax-mp
    @5
    @2
    cr
    wcel
    nmopadjle.1
    cT
    nmopre
    ax-mp
    letri3i
    mpbir2an
end
