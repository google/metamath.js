include "caa.mm"
include "wcel.mm"
include "cdgraa.mm"
include "cfv.mm"
include "cn.mm"
include "cv.mm"
include "cdgr.mm"
include "wceq.mm"
include "cc0.mm"
include "wa.mm"
include "cq.mm"
include "cply.mm"
include "c0p.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "dgraalem.mm"
include "simpld.mm"

theorem dgraacl
  let cA: class A
  let vd: setvar d
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cP: class P


  assert |- ( A e. AA -> ( degAA ` A ) e. NN )

  proof
    cA
    caa
    wcel
    cA
    cdgraa
    cfv
    #
    cn
    wcel
    va
    cv
    #
    cdgr
    cfv
    @0
    wceq
    cA
    @1
    cfv
    cc0
    wceq
    wa
    va
    cq
    cply
    cfv
    c0p
    csn
    cdif
    wrex
    cA
    va
    dgraalem
    simpld
end
