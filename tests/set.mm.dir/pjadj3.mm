include "cch.mm"
include "wcel.mm"
include "cpjh.mm"
include "cfv.mm"
include "crn.mm"
include "cado.mm"
include "wceq.mm"
include "wfn.mm"
include "pjmfn.mm"
include "fnfvelrn.mm"
include "mpan.mm"
include "pjadj2.mm"
include "syl.mm"

theorem pjadj3
  let cH: class H


  assert |- ( H e. CH -> ( adjh ` ( projh ` H ) ) = ( projh ` H ) )

  proof
    cH
    cch
    wcel
    #
    cH
    cpjh
    cfv
    #
    cpjh
    crn
    wcel
    #
    @1
    cado
    cfv
    @1
    wceq
    cpjh
    cch
    wfn
    @0
    @2
    pjmfn
    cch
    cH
    cpjh
    fnfvelrn
    mpan
    @1
    pjadj2
    syl
end
