include "cr.mm"
include "wcel.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "w3a.mm"
include "wa.mm"
include "cxr.mm"
include "wb.mm"
include "pnfxr.mm"
include "elico2.mm"
include "mpan2.mm"
include "ltpnf.mm"
include "adantr.mm"
include "pm4.71i.mm"
include "df-3an.mm"
include "bitr4i.mm"
include "syl6bbr.mm"

theorem elicopnf
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. RR -> ( B e. ( A [,) +oo ) <-> ( B e. RR /\ A <_ B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cA
    cpnf
    cico
    co
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    cle
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
    elico2
    mpan2
    @6
    @6
    @4
    wa
    @5
    @6
    @4
    @2
    @4
    @3
    cB
    ltpnf
    adantr
    pm4.71i
    @2
    @3
    @4
    df-3an
    bitr4i
    syl6bbr
end
