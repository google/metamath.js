include "c0.mm"
include "bj-csngl.mm"
include "csn.mm"
include "cun.mm"
include "bj-ctag.mm"
include "wcel.mm"
include "wo.mm"
include "0ex.mm"
include "snid.mm"
include "olci.mm"
include "elun.mm"
include "mpbir.mm"
include "df-bj-tag.mm"
include "eleqtrri.mm"

theorem bj-0eltag
  let cA: class A


  assert |- (/) e. tag A

  proof
    c0
    cA
    bj-csngl
    #
    c0
    csn
    #
    cun
    #
    cA
    bj-ctag
    c0
    @2
    wcel
    c0
    @0
    wcel
    #
    c0
    @1
    wcel
    #
    wo
    @4
    @3
    c0
    0ex
    snid
    olci
    c0
    @0
    @1
    elun
    mpbir
    cA
    df-bj-tag
    eleqtrri
end
