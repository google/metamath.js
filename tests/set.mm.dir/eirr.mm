include "ceu.mm"
include "cq.mm"
include "wcel.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cn.mm"
include "wrex.mm"
include "cz.mm"
include "wa.mm"
include "cn0.mm"
include "c1.mm"
include "cfa.mm"
include "cfv.mm"
include "cmpt.mm"
include "eqid.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "eirrlem.mm"
include "imnani.mm"
include "nrexdv.mm"
include "nrex.mm"
include "elq.mm"
include "mtbir.mm"
include "nelir.mm"

theorem eirr
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q


  assert |- _e e/ QQ

  proof
    ceu
    cq
    ceu
    cq
    wcel
    ceu
    vp
    cv
    #
    vq
    cv
    #
    cdiv
    co
    wceq
    #
    vq
    cn
    wrex
    #
    vp
    cz
    wrex
    @3
    vp
    cz
    @0
    cz
    wcel
    #
    @2
    vq
    cn
    @4
    @1
    cn
    wcel
    #
    wa
    #
    @2
    @6
    @2
    wa
    @0
    @1
    vn
    vn
    cn0
    c1
    vn
    cv
    cfa
    cfv
    cdiv
    co
    cmpt
    #
    @7
    eqid
    @4
    @5
    @2
    simpll
    @4
    @5
    @2
    simplr
    @6
    @2
    simpr
    eirrlem
    imnani
    nrexdv
    nrex
    vp
    vq
    ceu
    elq
    mtbir
    nelir
end
