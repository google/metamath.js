include "cdioph.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "cv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cres.mm"
include "wceq.mm"
include "cc0.mm"
include "wa.mm"
include "cmap.mm"
include "wrex.mm"
include "cab.mm"
include "cmzp.mm"
include "cuz.mm"
include "eldiophb.mm"
include "simplbi.mm"

theorem eldiophelnn0
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d


  assert |- ( A e. ( Dioph ` B ) -> B e. NN0 )

  proof
    cA
    cB
    cdioph
    cfv
    wcel
    cB
    cn0
    wcel
    cA
    vc
    cv
    vd
    cv
    #
    c1
    cB
    cfz
    co
    cres
    wceq
    @0
    va
    cv
    cfv
    cc0
    wceq
    wa
    vd
    cn0
    c1
    vb
    cv
    cfz
    co
    #
    cmap
    co
    wrex
    vc
    cab
    wceq
    va
    @1
    cmzp
    cfv
    wrex
    vb
    cB
    cuz
    cfv
    wrex
    vd
    vc
    cA
    vb
    cB
    va
    eldiophb
    simplbi
end
