include "chil.mm"
include "wf.mm"
include "cnop.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "cpnf.mm"
include "wceq.mm"
include "wn.mm"
include "wb.mm"
include "wo.mm"
include "cmnf.mm"
include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "nmoprepnf.mm"
include "df-ne.mm"
include "syl6bb.mm"
include "xor3.mm"
include "nbior.mm"
include "sylbir.mm"
include "mnfltxr.mm"
include "3syl.mm"

theorem nmopgtmnf
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( T : ~H --> ~H -> -oo < ( normop ` T ) )

  proof
    chil
    chil
    cT
    wf
    #
    cT
    cnop
    cfv
    #
    cr
    wcel
    #
    @1
    cpnf
    wceq
    #
    wn
    #
    wb
    #
    @2
    @3
    wo
    #
    cmnf
    @1
    clt
    wbr
    @0
    @2
    @1
    cpnf
    wne
    @4
    cT
    nmoprepnf
    @1
    cpnf
    df-ne
    syl6bb
    @5
    @2
    @3
    wb
    wn
    @6
    @2
    @3
    xor3
    @2
    @3
    nbior
    sylbir
    @1
    mnfltxr
    3syl
end
