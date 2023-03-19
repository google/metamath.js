include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cpr.mm"
include "wss.mm"
include "1nn.mm"
include "cz.mm"
include "nnz.mm"
include "1dvds.mm"
include "syl.mm"
include "wa.mm"
include "breq1.mm"
include "elrab.mm"
include "biimpri.mm"
include "sylancr.mm"
include "iddvds.mm"
include "mpdan.mm"
include "prssi.mm"
include "syl2anc.mm"

theorem 1idssfct
  let vn: setvar n
  let cN: class N

  disjoint N n
  assert |- ( N e. NN -> { 1 , N } C_ { n e. NN | n || N } )

  proof
    cN
    cn
    wcel
    #
    c1
    vn
    cv
    #
    cN
    cdvds
    wbr
    #
    vn
    cn
    crab
    #
    wcel
    #
    cN
    @3
    wcel
    #
    c1
    cN
    cpr
    @3
    wss
    @0
    c1
    cn
    wcel
    #
    c1
    cN
    cdvds
    wbr
    #
    @4
    1nn
    @0
    cN
    cz
    wcel
    #
    @7
    cN
    nnz
    #
    cN
    1dvds
    syl
    @4
    @6
    @7
    wa
    @2
    @7
    vn
    c1
    cn
    @1
    c1
    cN
    cdvds
    breq1
    elrab
    biimpri
    sylancr
    @0
    cN
    cN
    cdvds
    wbr
    #
    @5
    @0
    @8
    @10
    @9
    cN
    iddvds
    syl
    @5
    @0
    @10
    wa
    @2
    @10
    vn
    cN
    cn
    @1
    cN
    cN
    cdvds
    breq1
    elrab
    biimpri
    mpdan
    c1
    cN
    @3
    prssi
    syl2anc
end
