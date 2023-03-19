include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "ccxp.mm"
include "co.mm"
include "wceq.mm"
include "c1.mm"
include "cif.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "ce.mm"
include "cc.mm"
include "recn.mm"
include "cxpval.mm"
include "syl2an.mm"
include "3adant2.mm"
include "wa.mm"
include "1re.mm"
include "0re.mm"
include "keepel.mm"
include "a1i.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "simpl3.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "ne0gt0d.mm"
include "elrpd.mm"
include "relogcld.mm"
include "remulcld.mm"
include "reefcld.mm"
include "sylan2br.mm"
include "ifclda.mm"
include "eqeltrd.mm"

theorem recxpcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ 0 <_ A /\ B e. RR ) -> ( A ^c B ) e. RR )

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
    cB
    cr
    wcel
    #
    w3a
    #
    cA
    cB
    ccxp
    co
    #
    cA
    cc0
    wceq
    #
    cB
    cc0
    wceq
    #
    c1
    cc0
    cif
    #
    cB
    cA
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cif
    #
    cr
    @0
    @2
    @4
    @11
    wceq
    #
    @1
    @0
    cA
    cc
    wcel
    cB
    cc
    wcel
    @12
    @2
    cA
    recn
    cB
    recn
    cA
    cB
    cxpval
    syl2an
    3adant2
    @3
    @5
    @7
    @10
    cr
    @7
    cr
    wcel
    @3
    @5
    wa
    @6
    c1
    cc0
    cr
    1re
    0re
    keepel
    a1i
    @5
    wn
    @3
    cA
    cc0
    wne
    #
    @10
    cr
    wcel
    cA
    cc0
    df-ne
    @3
    @13
    wa
    #
    @9
    @14
    cB
    @8
    @0
    @1
    @2
    @13
    simpl3
    @14
    cA
    @14
    cA
    @0
    @1
    @2
    @13
    simpl1
    #
    @14
    cA
    @15
    @0
    @1
    @2
    @13
    simpl2
    @3
    @13
    simpr
    ne0gt0d
    elrpd
    relogcld
    remulcld
    reefcld
    sylan2br
    ifclda
    eqeltrd
end
