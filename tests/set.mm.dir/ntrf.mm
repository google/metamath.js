include "ctop.mm"
include "wcel.mm"
include "cpw.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wf.mm"
include "cv.mm"
include "cin.mm"
include "cuni.mm"
include "cmpt.mm"
include "vpwex.mm"
include "inex2.mm"
include "uniex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "cnt.mm"
include "cfv.mm"
include "ntrfval.mm"
include "syl5eq.mm"
include "fneq1d.mm"
include "mpbiri.mm"
include "ntrrn.mm"
include "df-f.mm"
include "sylanbrc.mm"

theorem ntrf
  let cI: class I
  let cJ: class J
  let cX: class X
  let vs: setvar s
  assume ntrrn.x: |- X = U. J
  assume ntrrn.i: |- I = ( int ` J )


  assert |- ( J e. Top -> I : ~P X --> J )

  proof
    cJ
    ctop
    wcel
    #
    cI
    cX
    cpw
    #
    wfn
    #
    cI
    crn
    cJ
    wss
    @1
    cJ
    cI
    wf
    @0
    @2
    vs
    @1
    cJ
    vs
    cv
    cpw
    #
    cin
    #
    cuni
    #
    cmpt
    #
    @1
    wfn
    vs
    @1
    @5
    @6
    @4
    @3
    cJ
    vs
    vpwex
    inex2
    uniex
    @6
    eqid
    fnmpti
    @0
    @1
    cI
    @6
    @0
    cI
    cJ
    cnt
    cfv
    @6
    ntrrn.i
    vs
    cJ
    cX
    ntrrn.x
    ntrfval
    syl5eq
    fneq1d
    mpbiri
    cI
    cJ
    cX
    ntrrn.x
    ntrrn.i
    ntrrn
    @1
    cJ
    cI
    df-f
    sylanbrc
end
