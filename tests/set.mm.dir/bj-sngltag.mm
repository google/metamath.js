include "wcel.mm"
include "csn.mm"
include "bj-csngl.mm"
include "bj-ctag.mm"
include "bj-sngltagi.mm"
include "c0.mm"
include "cun.mm"
include "df-bj-tag.mm"
include "eleq2i.mm"
include "wo.mm"
include "elun.mm"
include "idd.mm"
include "wceq.mm"
include "elsni.mm"
include "cvv.mm"
include "wn.mm"
include "snprc.mm"
include "elex.mm"
include "pm2.24d.mm"
include "syl5bir.mm"
include "syl5.mm"
include "jaod.mm"
include "syl5bi.mm"
include "impbid2.mm"

theorem bj-sngltag
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( { A } e. sngl B <-> { A } e. tag B ) )

  proof
    cA
    cV
    wcel
    #
    cA
    csn
    #
    cB
    bj-csngl
    #
    wcel
    #
    @1
    cB
    bj-ctag
    #
    wcel
    #
    @1
    cB
    bj-sngltagi
    @5
    @1
    @2
    c0
    csn
    #
    cun
    #
    wcel
    #
    @0
    @3
    @4
    @7
    @1
    cB
    df-bj-tag
    eleq2i
    @8
    @3
    @1
    @6
    wcel
    #
    wo
    @0
    @3
    @1
    @2
    @6
    elun
    @0
    @3
    @3
    @9
    @0
    @3
    idd
    @9
    @1
    c0
    wceq
    #
    @0
    @3
    @1
    c0
    elsni
    @10
    cA
    cvv
    wcel
    #
    wn
    @0
    @3
    cA
    snprc
    @0
    @11
    @3
    cA
    cV
    elex
    pm2.24d
    syl5bir
    syl5
    jaod
    syl5bi
    syl5bi
    impbid2
end
