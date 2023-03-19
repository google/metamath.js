include "cxr.mm"
include "wcel.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "wa.mm"
include "wb.mm"
include "pnfxr.mm"
include "elioo2.mm"
include "mpan2.mm"
include "df-3an.mm"
include "ltpnf.mm"
include "adantr.mm"
include "pm4.71i.mm"
include "bitr4i.mm"
include "syl6bb.mm"

theorem elioopnf
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. RR* -> ( B e. ( A (,) +oo ) <-> ( B e. RR /\ A < B ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cA
    cpnf
    cioo
    co
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    cB
    cpnf
    clt
    wbr
    #
    w3a
    #
    @2
    @3
    wa
    #
    @0
    cpnf
    cxr
    wcel
    @1
    @5
    wb
    pnfxr
    cA
    cpnf
    cB
    elioo2
    mpan2
    @5
    @6
    @4
    wa
    @6
    @2
    @3
    @4
    df-3an
    @6
    @4
    @2
    @4
    @3
    cB
    ltpnf
    adantr
    pm4.71i
    bitr4i
    syl6bb
end
