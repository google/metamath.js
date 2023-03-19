include "wcel.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "ccda.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "c1o.mm"
include "cun.mm"
include "cen.mm"
include "cdaval.mm"
include "3adant3.mm"
include "wbr.mm"
include "wa.mm"
include "cvv.mm"
include "0ex.mm"
include "xpsneng.mm"
include "mpan2.mm"
include "con0.mm"
include "1on.mm"
include "anim12i.mm"
include "xp01disj.mm"
include "jctl.mm"
include "unen.mm"
include "syl2an.mm"
include "3impa.mm"
include "eqbrtrd.mm"

theorem cdaun
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W /\ ( A i^i B ) = (/) ) -> ( A +c B ) ~~ ( A u. B ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cA
    cB
    cin
    c0
    wceq
    #
    w3a
    cA
    cB
    ccda
    co
    #
    cA
    c0
    csn
    cxp
    #
    cB
    c1o
    csn
    cxp
    #
    cun
    #
    cA
    cB
    cun
    #
    cen
    @0
    @1
    @3
    @6
    wceq
    @2
    cA
    cB
    cV
    cW
    cdaval
    3adant3
    @0
    @1
    @2
    @6
    @7
    cen
    wbr
    #
    @0
    @1
    wa
    @4
    cA
    cen
    wbr
    #
    @5
    cB
    cen
    wbr
    #
    wa
    @4
    @5
    cin
    c0
    wceq
    #
    @2
    wa
    @8
    @2
    @0
    @9
    @1
    @10
    @0
    c0
    cvv
    wcel
    @9
    0ex
    cA
    c0
    cV
    cvv
    xpsneng
    mpan2
    @1
    c1o
    con0
    wcel
    @10
    1on
    cB
    c1o
    cW
    con0
    xpsneng
    mpan2
    anim12i
    @2
    @11
    cA
    cB
    xp01disj
    jctl
    @4
    cA
    @5
    cB
    unen
    syl2an
    3impa
    eqbrtrd
end
