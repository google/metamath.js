include "c0.mm"
include "cop.mm"
include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "cpr.mm"
include "wo.mm"
include "id.mm"
include "cvv.mm"
include "wa.mm"
include "oprcl.mm"
include "dfopg.mm"
include "syl.mm"
include "eleqtrd.mm"
include "elpri.mm"
include "wne.mm"
include "wn.mm"
include "simpld.mm"
include "snnzg.mm"
include "necomd.mm"
include "prnzg.mm"
include "jca.mm"
include "neanior.mm"
include "sylib.mm"
include "pm2.65i.mm"

theorem 0nelop
  let cA: class A
  let cB: class B


  assert |- -. (/) e. <. A , B >.

  proof
    c0
    cA
    cB
    cop
    #
    wcel
    #
    c0
    cA
    csn
    #
    wceq
    c0
    cA
    cB
    cpr
    #
    wceq
    wo
    #
    @1
    c0
    @2
    @3
    cpr
    #
    wcel
    @4
    @1
    c0
    @0
    @5
    @1
    id
    @1
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    @0
    @5
    wceq
    cA
    cB
    c0
    oprcl
    #
    cA
    cB
    cvv
    cvv
    dfopg
    syl
    eleqtrd
    c0
    @2
    @3
    elpri
    syl
    @1
    c0
    @2
    wne
    #
    c0
    @3
    wne
    #
    wa
    @4
    wn
    @1
    @9
    @10
    @1
    @2
    c0
    @1
    @6
    @2
    c0
    wne
    @1
    @6
    @7
    @8
    simpld
    #
    cA
    cvv
    snnzg
    syl
    necomd
    @1
    @3
    c0
    @1
    @6
    @3
    c0
    wne
    @11
    cA
    cB
    cvv
    prnzg
    syl
    necomd
    jca
    c0
    @2
    c0
    @3
    neanior
    sylib
    pm2.65i
end
