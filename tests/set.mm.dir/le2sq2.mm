include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "simprr.mm"
include "wb.mm"
include "simprl.mm"
include "wi.mm"
include "0re.mm"
include "letr.mm"
include "mp3an1.mm"
include "exp4b.mm"
include "com23.mm"
include "imp43.mm"
include "jca.mm"
include "le2sq.mm"
include "syldan.mm"
include "mpbid.mm"

theorem le2sq2
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ ( B e. RR /\ A <_ B ) ) -> ( A ^ 2 ) <_ ( B ^ 2 ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
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
    wa
    #
    wa
    #
    @4
    cA
    c2
    cexp
    co
    cB
    c2
    cexp
    co
    cle
    wbr
    #
    @2
    @3
    @4
    simprr
    @2
    @5
    @3
    cc0
    cB
    cle
    wbr
    #
    wa
    @4
    @7
    wb
    @6
    @3
    @8
    @2
    @3
    @4
    simprl
    @0
    @1
    @3
    @4
    @8
    @0
    @3
    @1
    @4
    @8
    wi
    @0
    @3
    @1
    @4
    @8
    cc0
    cr
    wcel
    @0
    @3
    @1
    @4
    wa
    @8
    wi
    0re
    cc0
    cA
    cB
    letr
    mp3an1
    exp4b
    com23
    imp43
    jca
    cA
    cB
    le2sq
    syldan
    mpbid
end
