include "cado.mm"
include "cfv.mm"
include "ccom.mm"
include "cnop.mm"
include "cc0.mm"
include "wceq.mm"
include "ch0o.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "nmopcoadj2i.mm"
include "eqeq1i.mm"
include "cbo.mm"
include "wcel.mm"
include "cr.mm"
include "nmopre.mm"
include "ax-mp.mm"
include "recni.mm"
include "sqeq0i.mm"
include "bitri.mm"
include "clo.mm"
include "bdopln.mm"
include "adjbdln.mm"
include "lnopcoi.mm"
include "nmlnop0iHIL.mm"
include "3bitr3i.mm"

theorem nmopcoadj0i
  let cT: class T
  let vx: setvar x
  assume nmopcoadj.1: |- T e. BndLinOp


  assert |- ( ( T o. ( adjh ` T ) ) = 0hop <-> T = 0hop )

  proof
    cT
    cT
    cado
    cfv
    #
    ccom
    #
    cnop
    cfv
    #
    cc0
    wceq
    #
    cT
    cnop
    cfv
    #
    cc0
    wceq
    #
    @1
    ch0o
    wceq
    cT
    ch0o
    wceq
    @3
    @4
    c2
    cexp
    co
    #
    cc0
    wceq
    @5
    @2
    @6
    cc0
    cT
    nmopcoadj.1
    nmopcoadj2i
    eqeq1i
    @4
    @4
    cT
    cbo
    wcel
    #
    @4
    cr
    wcel
    nmopcoadj.1
    cT
    nmopre
    ax-mp
    recni
    sqeq0i
    bitri
    @1
    cT
    @0
    @7
    cT
    clo
    wcel
    nmopcoadj.1
    cT
    bdopln
    ax-mp
    #
    @0
    cbo
    wcel
    #
    @0
    clo
    wcel
    @7
    @9
    nmopcoadj.1
    cT
    adjbdln
    ax-mp
    @0
    bdopln
    ax-mp
    lnopcoi
    nmlnop0iHIL
    cT
    @8
    nmlnop0iHIL
    3bitr3i
end
