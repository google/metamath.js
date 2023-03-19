include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cpw.mm"
include "crest.mm"
include "co.mm"
include "cv.mm"
include "ctop.mm"
include "wb.mm"
include "distop.mm"
include "adantr.mm"
include "elpw2g.mm"
include "biimpar.mm"
include "restopn2.mm"
include "syl2anc.mm"
include "selpw.mm"
include "wi.mm"
include "sstr.mm"
include "expcom.mm"
include "adantl.mm"
include "syl6ibr.mm"
include "pm4.71rd.mm"
include "syl5bb.mm"
include "bitr4d.mm"
include "eqrdv.mm"

theorem restdis
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x


  assert |- ( ( A e. V /\ B C_ A ) -> ( ~P A |`t B ) = ~P B )

  proof
    cA
    cV
    wcel
    #
    cB
    cA
    wss
    #
    wa
    #
    vx
    cA
    cpw
    #
    cB
    crest
    co
    #
    cB
    cpw
    #
    @2
    vx
    cv
    #
    @4
    wcel
    #
    @6
    @3
    wcel
    #
    @6
    cB
    wss
    #
    wa
    #
    @6
    @5
    wcel
    #
    @2
    @3
    ctop
    wcel
    #
    cB
    @3
    wcel
    #
    @7
    @10
    wb
    @0
    @12
    @1
    cA
    cV
    distop
    adantr
    @0
    @13
    @1
    cB
    cA
    cV
    elpw2g
    biimpar
    cB
    @6
    @3
    restopn2
    syl2anc
    @11
    @9
    @2
    @10
    vx
    cB
    selpw
    @2
    @9
    @8
    @2
    @9
    @6
    cA
    wss
    #
    @8
    @1
    @9
    @14
    wi
    @0
    @9
    @1
    @14
    @6
    cB
    cA
    sstr
    expcom
    adantl
    vx
    cA
    selpw
    syl6ibr
    pm4.71rd
    syl5bb
    bitr4d
    eqrdv
end
