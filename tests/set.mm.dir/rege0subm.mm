include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "cr.mm"
include "rge0ssre.mm"
include "sseli.mm"
include "recnd.mm"
include "ge0addcl.mm"
include "0e0icopnf.mm"
include "cnsubmlem.mm"

theorem rege0subm
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R


  assert |- ( 0 [,) +oo ) e. ( SubMnd ` CCfld )

  proof
    vx
    vy
    cc0
    cpnf
    cico
    co
    #
    vx
    cv
    #
    @0
    wcel
    @1
    @0
    cr
    @1
    rge0ssre
    sseli
    recnd
    @1
    vy
    cv
    ge0addcl
    0e0icopnf
    cnsubmlem
end
