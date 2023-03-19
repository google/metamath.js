include "cr.mm"
include "ccld.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "crest.mm"
include "co.mm"
include "recld2.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "tgioo2.mm"
include "eqcomi.mm"
include "zcld.mm"
include "restcldr.mm"
include "mp2an.mm"

theorem zcld2
  let cJ: class J
  let vn: setvar n
  let vr: setvar r
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let cS: class S
  assume recld2.1: |- J = ( TopOpen ` CCfld )


  assert |- ZZ e. ( Clsd ` J )

  proof
    cr
    cJ
    ccld
    cfv
    #
    wcel
    cz
    cJ
    cr
    crest
    co
    #
    ccld
    cfv
    wcel
    cz
    @0
    wcel
    cJ
    recld2.1
    recld2
    @1
    cioo
    crn
    ctg
    cfv
    @1
    cJ
    recld2.1
    tgioo2
    eqcomi
    zcld
    cr
    cz
    cJ
    restcldr
    mp2an
end
