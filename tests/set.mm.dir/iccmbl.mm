include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cicc.mm"
include "co.mm"
include "cdif.mm"
include "cvol.mm"
include "cdm.mm"
include "wss.mm"
include "wceq.mm"
include "iccssre.mm"
include "dfss4.mm"
include "sylib.mm"
include "cmnf.mm"
include "cioo.mm"
include "cpnf.mm"
include "cun.mm"
include "difreicc.mm"
include "ioombl.mm"
include "unmbl.mm"
include "mp2an.mm"
include "syl6eqel.mm"
include "cmmbl.mm"
include "syl.mm"
include "eqeltrrd.mm"

theorem iccmbl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A [,] B ) e. dom vol )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    wa
    #
    cr
    cr
    cA
    cB
    cicc
    co
    #
    cdif
    #
    cdif
    #
    @1
    cvol
    cdm
    #
    @0
    @1
    cr
    wss
    @3
    @1
    wceq
    cA
    cB
    iccssre
    @1
    cr
    dfss4
    sylib
    @0
    @2
    @4
    wcel
    @3
    @4
    wcel
    @0
    @2
    cmnf
    cA
    cioo
    co
    #
    cB
    cpnf
    cioo
    co
    #
    cun
    #
    @4
    cA
    cB
    difreicc
    @5
    @4
    wcel
    @6
    @4
    wcel
    @7
    @4
    wcel
    cmnf
    cA
    ioombl
    cB
    cpnf
    ioombl
    @5
    @6
    unmbl
    mp2an
    syl6eqel
    @2
    cmmbl
    syl
    eqeltrrd
end
