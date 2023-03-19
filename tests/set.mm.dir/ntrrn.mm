include "ctop.mm"
include "wcel.mm"
include "crn.mm"
include "cnt.mm"
include "cfv.mm"
include "rneqi.mm"
include "cpw.mm"
include "wfn.mm"
include "cv.mm"
include "wral.mm"
include "wss.mm"
include "cin.mm"
include "cuni.mm"
include "cmpt.mm"
include "cvv.mm"
include "vpwex.mm"
include "inex2.mm"
include "uniex.mm"
include "rgenw.mm"
include "nfcv.mm"
include "fnmptf.mm"
include "mp1i.mm"
include "ntrfval.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "elpwi.mm"
include "ntropn.mm"
include "ex.mm"
include "syl5.mm"
include "ralrimiv.mm"
include "fnfvrnss.mm"
include "syl2anc.mm"
include "syl5eqss.mm"

theorem ntrrn
  let cI: class I
  let cJ: class J
  let cX: class X
  let vs: setvar s
  assume ntrrn.x: |- X = U. J
  assume ntrrn.i: |- I = ( int ` J )


  assert |- ( J e. Top -> ran I C_ J )

  proof
    cJ
    ctop
    wcel
    #
    cI
    crn
    cJ
    cnt
    cfv
    #
    crn
    #
    cJ
    cI
    @1
    ntrrn.i
    rneqi
    @0
    @1
    cX
    cpw
    #
    wfn
    #
    vs
    cv
    #
    @1
    cfv
    cJ
    wcel
    #
    vs
    @3
    wral
    @2
    cJ
    wss
    @0
    @4
    vs
    @3
    cJ
    @5
    cpw
    #
    cin
    #
    cuni
    #
    cmpt
    #
    @3
    wfn
    #
    @9
    cvv
    wcel
    #
    vs
    @3
    wral
    @11
    @0
    @12
    vs
    @3
    @8
    @7
    cJ
    vs
    vpwex
    inex2
    uniex
    rgenw
    vs
    @3
    @9
    cvv
    vs
    @3
    nfcv
    fnmptf
    mp1i
    @0
    @3
    @1
    @10
    vs
    cJ
    cX
    ntrrn.x
    ntrfval
    fneq1d
    mpbird
    @0
    @6
    vs
    @3
    @5
    @3
    wcel
    @5
    cX
    wss
    #
    @0
    @6
    @5
    cX
    elpwi
    @0
    @13
    @6
    @5
    cJ
    cX
    ntrrn.x
    ntropn
    ex
    syl5
    ralrimiv
    vs
    @3
    cJ
    @1
    fnfvrnss
    syl2anc
    syl5eqss
end
