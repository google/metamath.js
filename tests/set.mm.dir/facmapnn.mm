include "cn.mm"
include "cv.mm"
include "cfa.mm"
include "cfv.mm"
include "cmpt.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "eqid.mm"
include "cn0.mm"
include "nnnn0.mm"
include "faccl.mm"
include "syl.mm"
include "fmpti.mm"
include "nnex.mm"
include "elmap.mm"
include "mpbir.mm"

theorem facmapnn
  let vn: setvar n


  assert |- ( n e. NN |-> ( ! ` n ) ) e. ( NN ^m NN )

  proof
    vn
    cn
    vn
    cv
    #
    cfa
    cfv
    #
    cmpt
    #
    cn
    cn
    cmap
    co
    wcel
    cn
    cn
    @2
    wf
    vn
    cn
    cn
    @1
    @2
    @2
    eqid
    @0
    cn
    wcel
    @0
    cn0
    wcel
    @1
    cn
    wcel
    @0
    nnnn0
    @0
    faccl
    syl
    fmpti
    cn
    cn
    @2
    nnex
    nnex
    elmap
    mpbir
end
