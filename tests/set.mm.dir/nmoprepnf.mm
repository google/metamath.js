include "chil.mm"
include "wf.mm"
include "cv.mm"
include "cno.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cr.mm"
include "wcel.mm"
include "cpnf.mm"
include "wne.mm"
include "cnop.mm"
include "wss.mm"
include "c0.mm"
include "wb.mm"
include "nmopsetretHIL.mm"
include "c0v.mm"
include "nmopsetn0.mm"
include "ne0ii.mm"
include "supxrre2.mm"
include "sylancl.mm"
include "nmopval.mm"
include "eleq1d.mm"
include "neeq1d.mm"
include "3bitr4d.mm"

theorem nmoprepnf
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( T : ~H --> ~H -> ( ( normop ` T ) e. RR <-> ( normop ` T ) =/= +oo ) )

  proof
    chil
    chil
    cT
    wf
    #
    vy
    cv
    #
    cno
    cfv
    c1
    cle
    wbr
    vx
    cv
    @1
    cT
    cfv
    cno
    cfv
    wceq
    wa
    vy
    chil
    wrex
    vx
    cab
    #
    cxr
    clt
    csup
    #
    cr
    wcel
    #
    @3
    cpnf
    wne
    #
    cT
    cnop
    cfv
    #
    cr
    wcel
    @6
    cpnf
    wne
    @0
    @2
    cr
    wss
    @2
    c0
    wne
    @4
    @5
    wb
    vx
    vy
    cT
    nmopsetretHIL
    c0v
    cT
    cfv
    cno
    cfv
    @2
    vx
    vy
    cT
    nmopsetn0
    ne0ii
    @2
    supxrre2
    sylancl
    @0
    @6
    @3
    cr
    vx
    vy
    cT
    nmopval
    #
    eleq1d
    @0
    @6
    @3
    cpnf
    @7
    neeq1d
    3bitr4d
end
