include "ctop.mm"
include "wcel.mm"
include "cpw.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "wf.mm"
include "ccld.mm"
include "cfv.mm"
include "ccl.mm"
include "clsf.mm"
include "feq1i.mm"
include "df-f.mm"
include "sylbb1.mm"
include "cldss2.mm"
include "sstr2.mm"
include "mpi.mm"
include "anim2i.mm"
include "3syl.mm"
include "sylibr.mm"

theorem clsf2
  let cJ: class J
  let cK: class K
  let cX: class X
  assume clselmap.x: |- X = U. J
  assume clselmap.k: |- K = ( cls ` J )


  assert |- ( J e. Top -> K : ~P X --> ~P X )

  proof
    cJ
    ctop
    wcel
    #
    cK
    cX
    cpw
    #
    wfn
    #
    cK
    crn
    #
    @1
    wss
    #
    wa
    #
    @1
    @1
    cK
    wf
    @0
    @1
    cJ
    ccld
    cfv
    #
    cJ
    ccl
    cfv
    #
    wf
    #
    @2
    @3
    @6
    wss
    #
    wa
    #
    @5
    cJ
    cX
    clselmap.x
    clsf
    @1
    @6
    cK
    wf
    @8
    @10
    @1
    @6
    cK
    @7
    clselmap.k
    feq1i
    @1
    @6
    cK
    df-f
    sylbb1
    @9
    @4
    @2
    @9
    @6
    @1
    wss
    @4
    cJ
    cX
    clselmap.x
    cldss2
    @3
    @6
    @1
    sstr2
    mpi
    anim2i
    3syl
    @1
    @1
    cK
    df-f
    sylibr
end
