include "wcel.mm"
include "c0.mm"
include "cmap.mm"
include "co.mm"
include "c1o.mm"
include "cv.mm"
include "wf.mm"
include "cvv.mm"
include "wb.mm"
include "0ex.mm"
include "elmapg.mm"
include "mpan2.mm"
include "wceq.mm"
include "f0bi.mm"
include "el1o.mm"
include "bitr4i.mm"
include "syl6bb.mm"
include "eqrdv.mm"

theorem map0e
  let cA: class A
  let cV: class V
  let vf: setvar f
  let cB: class B
  let cW: class W


  assert |- ( A e. V -> ( A ^m (/) ) = 1o )

  proof
    cA
    cV
    wcel
    #
    vf
    cA
    c0
    cmap
    co
    #
    c1o
    @0
    vf
    cv
    #
    @1
    wcel
    #
    c0
    cA
    @2
    wf
    #
    @2
    c1o
    wcel
    #
    @0
    c0
    cvv
    wcel
    @3
    @4
    wb
    0ex
    cA
    c0
    @2
    cV
    cvv
    elmapg
    mpan2
    @4
    @2
    c0
    wceq
    @5
    @2
    cA
    f0bi
    @2
    el1o
    bitr4i
    syl6bb
    eqrdv
end
