include "cxr.mm"
include "wcel.mm"
include "cmnf.mm"
include "cioo.mm"
include "co.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "wa.mm"
include "wb.mm"
include "mnfxr.mm"
include "elioo2.mm"
include "mpan.mm"
include "an32.mm"
include "df-3an.mm"
include "mnflt.mm"
include "adantr.mm"
include "pm4.71i.mm"
include "3bitr4i.mm"
include "syl6bb.mm"

theorem elioomnf
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. RR* -> ( B e. ( -oo (,) A ) <-> ( B e. RR /\ B < A ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cmnf
    cA
    cioo
    co
    wcel
    #
    cB
    cr
    wcel
    #
    cmnf
    cB
    clt
    wbr
    #
    cB
    cA
    clt
    wbr
    #
    w3a
    #
    @2
    @4
    wa
    #
    cmnf
    cxr
    wcel
    @0
    @1
    @5
    wb
    mnfxr
    cmnf
    cA
    cB
    elioo2
    mpan
    @2
    @3
    wa
    @4
    wa
    @6
    @3
    wa
    @5
    @6
    @2
    @3
    @4
    an32
    @2
    @3
    @4
    df-3an
    @6
    @3
    @2
    @3
    @4
    cB
    mnflt
    adantr
    pm4.71i
    3bitr4i
    syl6bb
end
