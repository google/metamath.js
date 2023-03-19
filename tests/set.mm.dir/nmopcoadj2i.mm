include "cado.mm"
include "cfv.mm"
include "ccom.mm"
include "cnop.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cbo.mm"
include "wcel.mm"
include "adjbdln.mm"
include "ax-mp.mm"
include "nmopcoadji.mm"
include "cdm.mm"
include "wceq.mm"
include "bdopadj.mm"
include "adjadj.mm"
include "coeq1i.mm"
include "fveq2i.mm"
include "nmopadji.mm"
include "oveq1i.mm"
include "3eqtr3i.mm"

theorem nmopcoadj2i
  let cT: class T
  let vx: setvar x
  assume nmopcoadj.1: |- T e. BndLinOp


  assert |- ( normop ` ( T o. ( adjh ` T ) ) ) = ( ( normop ` T ) ^ 2 )

  proof
    cT
    cado
    cfv
    #
    cado
    cfv
    #
    @0
    ccom
    #
    cnop
    cfv
    @0
    cnop
    cfv
    #
    c2
    cexp
    co
    cT
    @0
    ccom
    #
    cnop
    cfv
    cT
    cnop
    cfv
    #
    c2
    cexp
    co
    @0
    cT
    cbo
    wcel
    #
    @0
    cbo
    wcel
    nmopcoadj.1
    cT
    adjbdln
    ax-mp
    nmopcoadji
    @2
    @4
    cnop
    @1
    cT
    @0
    cT
    cado
    cdm
    wcel
    #
    @1
    cT
    wceq
    @6
    @7
    nmopcoadj.1
    cT
    bdopadj
    ax-mp
    cT
    adjadj
    ax-mp
    coeq1i
    fveq2i
    @3
    @5
    c2
    cexp
    cT
    nmopcoadj.1
    nmopadji
    oveq1i
    3eqtr3i
end
