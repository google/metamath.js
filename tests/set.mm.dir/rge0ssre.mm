include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cr.mm"
include "cv.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "elrege0.mm"
include "simplbi.mm"
include "ssriv.mm"

theorem rge0ssre
  let vx: setvar x


  assert |- ( 0 [,) +oo ) C_ RR

  proof
    vx
    cc0
    cpnf
    cico
    co
    #
    cr
    vx
    cv
    #
    @0
    wcel
    @1
    cr
    wcel
    cc0
    @1
    cle
    wbr
    @1
    elrege0
    simplbi
    ssriv
end
