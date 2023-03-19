include "wcel.mm"
include "cvv.mm"
include "cep.mm"
include "wbr.mm"
include "wi.mm"
include "cop.mm"
include "df-br.mm"
include "cv.mm"
include "copab.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "elopab.mm"
include "vex.mm"
include "pm3.2i.mm"
include "opeqex.mm"
include "mpbiri.mm"
include "simpld.mm"
include "adantr.mm"
include "exlimivv.mm"
include "sylbi.mm"
include "df-eprel.mm"
include "eleq2s.mm"
include "a1i.mm"
include "elex.mm"
include "wb.mm"
include "eleq12.mm"
include "brabga.mm"
include "expcom.mm"
include "pm5.21ndd.mm"

theorem epelg
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( B e. V -> ( A _E B <-> A e. B ) )

  proof
    cB
    cV
    wcel
    #
    cA
    cvv
    wcel
    #
    cA
    cB
    cep
    wbr
    #
    cA
    cB
    wcel
    #
    @2
    @1
    wi
    @0
    @2
    cA
    cB
    cop
    #
    cep
    wcel
    @1
    cA
    cB
    cep
    df-br
    @1
    @4
    vx
    cv
    #
    vy
    cv
    #
    wcel
    #
    vx
    vy
    copab
    #
    cep
    @4
    @8
    wcel
    @4
    @5
    @6
    cop
    wceq
    #
    @7
    wa
    #
    vy
    wex
    vx
    wex
    @1
    @7
    vx
    vy
    @4
    elopab
    @10
    @1
    vx
    vy
    @9
    @1
    @7
    @9
    @1
    cB
    cvv
    wcel
    #
    @9
    @1
    @11
    wa
    @5
    cvv
    wcel
    #
    @6
    cvv
    wcel
    #
    wa
    @12
    @13
    vx
    vex
    vy
    vex
    pm3.2i
    cA
    cB
    @5
    @6
    opeqex
    mpbiri
    simpld
    adantr
    exlimivv
    sylbi
    vx
    vy
    df-eprel
    #
    eleq2s
    sylbi
    a1i
    @3
    @1
    wi
    @0
    cA
    cB
    elex
    a1i
    @1
    @0
    @2
    @3
    wb
    @7
    @3
    vx
    vy
    cA
    cB
    cep
    cvv
    cV
    @5
    cA
    @6
    cB
    eleq12
    @14
    brabga
    expcom
    pm5.21ndd
end
