include "citg1.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "crn.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "ccnv.mm"
include "cima.mm"
include "cvol.mm"
include "cmul.mm"
include "co.mm"
include "csu.mm"
include "cr.mm"
include "itg1val.mm"
include "cfn.mm"
include "wss.mm"
include "i1frn.mm"
include "difss.mm"
include "ssfi.mm"
include "sylancl.mm"
include "wa.mm"
include "wf.mm"
include "i1ff.mm"
include "frn.mm"
include "syl.mm"
include "ssdifssd.mm"
include "sselda.mm"
include "i1fima2sn.mm"
include "remulcld.mm"
include "fsumrecl.mm"
include "eqeltrd.mm"

theorem itg1cl
  let cF: class F
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- ( F e. dom S.1 -> ( S.1 ` F ) e. RR )

  proof
    cF
    citg1
    cdm
    wcel
    #
    cF
    citg1
    cfv
    cF
    crn
    #
    cc0
    csn
    #
    cdif
    #
    vx
    cv
    #
    cF
    ccnv
    @4
    csn
    cima
    cvol
    cfv
    #
    cmul
    co
    #
    vx
    csu
    cr
    vx
    cF
    itg1val
    @0
    @3
    @6
    vx
    @0
    @1
    cfn
    wcel
    @3
    @1
    wss
    @3
    cfn
    wcel
    cF
    i1frn
    @1
    @2
    difss
    @1
    @3
    ssfi
    sylancl
    @0
    @4
    @3
    wcel
    wa
    @4
    @5
    @0
    @3
    cr
    @4
    @0
    @1
    cr
    @2
    @0
    cr
    cr
    cF
    wf
    @1
    cr
    wss
    cF
    i1ff
    cr
    cr
    cF
    frn
    syl
    ssdifssd
    sselda
    @4
    @1
    cF
    i1fima2sn
    remulcld
    fsumrecl
    eqeltrd
end
