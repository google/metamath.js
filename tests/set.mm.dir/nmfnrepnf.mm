include "chil.mm"
include "cc.mm"
include "wf.mm"
include "cv.mm"
include "cno.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
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
include "cnmf.mm"
include "wss.mm"
include "c0.mm"
include "wb.mm"
include "nmfnsetre.mm"
include "c0v.mm"
include "nmfnsetn0.mm"
include "ne0ii.mm"
include "supxrre2.mm"
include "sylancl.mm"
include "nmfnval.mm"
include "eleq1d.mm"
include "neeq1d.mm"
include "3bitr4d.mm"

theorem nmfnrepnf
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( T : ~H --> CC -> ( ( normfn ` T ) e. RR <-> ( normfn ` T ) =/= +oo ) )

  proof
    chil
    cc
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
    cabs
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
    cnmf
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
    nmfnsetre
    c0v
    cT
    cfv
    cabs
    cfv
    @2
    vx
    vy
    cT
    nmfnsetn0
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
    nmfnval
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
