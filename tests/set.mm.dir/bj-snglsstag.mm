include "bj-csngl.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "bj-ctag.mm"
include "ssun1.mm"
include "df-bj-tag.mm"
include "sseqtr4i.mm"

theorem bj-snglsstag
  let cA: class A


  assert |- sngl A C_ tag A

  proof
    cA
    bj-csngl
    #
    @0
    c0
    csn
    #
    cun
    cA
    bj-ctag
    @0
    @1
    ssun1
    cA
    df-bj-tag
    sseqtr4i
end
