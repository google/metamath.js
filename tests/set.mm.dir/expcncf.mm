include "cn0.mm"
include "wcel.mm"
include "cc.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cmpt.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "ccn.mm"
include "ccncf.mm"
include "eqid.mm"
include "expcn.mm"
include "cncfcn1.mm"
include "syl6eleqr.mm"

theorem expcncf
  let vx: setvar x
  let cN: class N

  disjoint N x
  assert |- ( N e. NN0 -> ( x e. CC |-> ( x ^ N ) ) e. ( CC -cn-> CC ) )

  proof
    cN
    cn0
    wcel
    vx
    cc
    vx
    cv
    cN
    cexp
    co
    cmpt
    ccnfld
    ctopn
    cfv
    #
    @0
    ccn
    co
    cc
    cc
    ccncf
    co
    vx
    @0
    cN
    @0
    eqid
    #
    expcn
    @0
    @1
    cncfcn1
    syl6eleqr
end
