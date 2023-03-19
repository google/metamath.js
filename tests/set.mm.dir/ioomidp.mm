include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cxr.mm"
include "rexr.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "wa.mm"
include "readdcl.mm"
include "rehalfcld.mm"
include "3adant3.mm"
include "avglt1.mm"
include "biimp3a.mm"
include "avglt2.mm"
include "eliood.mm"

theorem ioomidp
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR /\ A < B ) -> ( ( A + B ) / 2 ) e. ( A (,) B ) )

  proof
    cA
    cr
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
    w3a
    cA
    cB
    cA
    cB
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @0
    @1
    cA
    cxr
    wcel
    @2
    cA
    rexr
    3ad2ant1
    @1
    @0
    cB
    cxr
    wcel
    @2
    cB
    rexr
    3ad2ant2
    @0
    @1
    @4
    cr
    wcel
    @2
    @0
    @1
    wa
    @3
    cA
    cB
    readdcl
    rehalfcld
    3adant3
    @0
    @1
    @2
    cA
    @4
    clt
    wbr
    cA
    cB
    avglt1
    biimp3a
    @0
    @1
    @2
    @4
    cB
    clt
    wbr
    cA
    cB
    avglt2
    biimp3a
    eliood
end
