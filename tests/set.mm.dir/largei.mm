include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cst.mm"
include "wrex.mm"
include "c0h.mm"
include "wn.mm"
include "wral.mm"
include "ralnex.mm"
include "wi.mm"
include "wss.mm"
include "wcel.mm"
include "wb.mm"
include "cc0.mm"
include "ax-1ne0.mm"
include "neii.mm"
include "st0.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "mtbiri.mm"
include "mtt.mm"
include "syl.mm"
include "ralbiia.mm"
include "h0elch.mm"
include "strb.mm"
include "chle0i.mm"
include "3bitri.mm"
include "bitr3i.mm"
include "con1bii.mm"

theorem largei
  let cA: class A
  let vf: setvar f
  assume large.1: |- A e. CH

  disjoint A f
  assert |- ( -. A = 0H <-> E. f e. States ( f ` A ) = 1 )

  proof
    cA
    vf
    cv
    #
    cfv
    c1
    wceq
    #
    vf
    cst
    wrex
    #
    cA
    c0h
    wceq
    #
    @2
    wn
    @1
    wn
    #
    vf
    cst
    wral
    #
    @3
    @1
    vf
    cst
    ralnex
    @5
    @1
    c0h
    @0
    cfv
    #
    c1
    wceq
    #
    wi
    #
    vf
    cst
    wral
    cA
    c0h
    wss
    @3
    @4
    @8
    vf
    cst
    @0
    cst
    wcel
    #
    @7
    wn
    @4
    @8
    wb
    @9
    @7
    c1
    cc0
    wceq
    #
    c1
    cc0
    ax-1ne0
    neii
    @9
    @7
    cc0
    c1
    wceq
    @10
    @9
    @6
    cc0
    c1
    @0
    st0
    eqeq1d
    cc0
    c1
    eqcom
    syl6bb
    mtbiri
    @7
    @1
    mtt
    syl
    ralbiia
    cA
    c0h
    vf
    large.1
    h0elch
    strb
    cA
    large.1
    chle0i
    3bitri
    bitr3i
    con1bii
end
