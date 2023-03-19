include "cv.mm"
include "ctrls.mm"
include "cfv.mm"
include "wbr.mm"
include "c1.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cres.mm"
include "ccnv.mm"
include "wfun.mm"
include "cc0.mm"
include "cpr.mm"
include "cima.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "cvv.mm"
include "cpths.mm"
include "df-pths.mm"
include "relmptopab.mm"

theorem relpths
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p


  assert |- Rel ( Paths ` G )

  proof
    vf
    cv
    #
    vp
    cv
    #
    vg
    cv
    ctrls
    cfv
    wbr
    @1
    c1
    @0
    chash
    cfv
    #
    cfzo
    co
    #
    cres
    ccnv
    wfun
    @1
    cc0
    @2
    cpr
    cima
    @1
    @3
    cima
    cin
    c0
    wceq
    w3a
    vg
    vf
    vp
    cvv
    cG
    cpths
    vf
    vg
    vp
    df-pths
    relmptopab
end
