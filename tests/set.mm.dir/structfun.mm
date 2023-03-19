include "cstr.mm"
include "wbr.mm"
include "ccnv.mm"
include "wfun.mm"
include "structfung.mm"
include "ax-mp.mm"

theorem structfun
  let cF: class F
  let cX: class X
  assume structfun.1: |- F Struct X


  assert |- Fun `' `' F

  proof
    cF
    cX
    cstr
    wbr
    cF
    ccnv
    ccnv
    wfun
    structfun.1
    cF
    cX
    structfung
    ax-mp
end
