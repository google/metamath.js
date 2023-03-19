include "cn.mm"
include "wcel.mm"
include "cneg.mm"
include "cr.mm"
include "cc0.mm"
include "wceq.mm"
include "w3o.mm"
include "cz.mm"
include "nnre.mm"
include "renegcld.mm"
include "cc.mm"
include "nncn.mm"
include "negneg.mm"
include "eleq1d.mm"
include "biimprd.mm"
include "mpcom.mm"
include "3mix3d.mm"
include "elz.mm"
include "sylanbrc.mm"

theorem nnnegz
  let cN: class N


  assert |- ( N e. NN -> -u N e. ZZ )

  proof
    cN
    cn
    wcel
    #
    cN
    cneg
    #
    cr
    wcel
    @1
    cc0
    wceq
    #
    @1
    cn
    wcel
    #
    @1
    cneg
    #
    cn
    wcel
    #
    w3o
    @1
    cz
    wcel
    @0
    cN
    cN
    nnre
    renegcld
    @0
    @5
    @2
    @3
    cN
    cc
    wcel
    #
    @0
    @5
    cN
    nncn
    @6
    @5
    @0
    @6
    @4
    cN
    cn
    cN
    negneg
    eleq1d
    biimprd
    mpcom
    3mix3d
    @1
    elz
    sylanbrc
end
