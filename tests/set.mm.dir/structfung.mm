include "cstr.mm"
include "wbr.mm"
include "ccnv.mm"
include "wfun.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "structn0fun.mm"
include "structcnvcnv.mm"
include "funeqd.mm"
include "mpbird.mm"

theorem structfung
  let cF: class F
  let cX: class X


  assert |- ( F Struct X -> Fun `' `' F )

  proof
    cF
    cX
    cstr
    wbr
    #
    cF
    ccnv
    ccnv
    #
    wfun
    cF
    c0
    csn
    cdif
    #
    wfun
    cF
    cX
    structn0fun
    @0
    @1
    @2
    cF
    cX
    structcnvcnv
    funeqd
    mpbird
end
