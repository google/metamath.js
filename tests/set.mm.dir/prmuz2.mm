include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "isprm4.mm"
include "simplbi.mm"

theorem prmuz2
  let cP: class P
  let vx: setvar x


  assert |- ( P e. Prime -> P e. ( ZZ>= ` 2 ) )

  proof
    cP
    cprime
    wcel
    cP
    c2
    cuz
    cfv
    #
    wcel
    vx
    cv
    #
    cP
    cdvds
    wbr
    @1
    cP
    wceq
    wi
    vx
    @0
    wral
    vx
    cP
    isprm4
    simplbi
end
