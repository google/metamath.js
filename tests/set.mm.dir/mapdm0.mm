include "wcel.mm"
include "c0.mm"
include "cmap.mm"
include "co.mm"
include "csn.mm"
include "cv.mm"
include "wceq.mm"
include "wf.mm"
include "cvv.mm"
include "wb.mm"
include "0ex.mm"
include "elmapg.mm"
include "mpan2.mm"
include "f0bi.mm"
include "syl6bb.mm"
include "vex.mm"
include "elsn.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem mapdm0
  let cB: class B
  let cV: class V
  let vf: setvar f


  assert |- ( B e. V -> ( B ^m (/) ) = { (/) } )

  proof
    cB
    cV
    wcel
    #
    vf
    cB
    c0
    cmap
    co
    #
    c0
    csn
    #
    @0
    vf
    cv
    #
    @1
    wcel
    #
    @3
    c0
    wceq
    #
    @3
    @2
    wcel
    @0
    @4
    c0
    cB
    @3
    wf
    #
    @5
    @0
    c0
    cvv
    wcel
    @4
    @6
    wb
    0ex
    cB
    c0
    @3
    cV
    cvv
    elmapg
    mpan2
    @3
    cB
    f0bi
    syl6bb
    @3
    c0
    vf
    vex
    elsn
    syl6bbr
    eqrdv
end
