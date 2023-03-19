include "chst.mm"
include "wcel.mm"
include "cch.mm"
include "wa.mm"
include "wss.mm"
include "cfv.mm"
include "cno.mm"
include "c1.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "simpr.mm"
include "hstle.mm"
include "adantr.mm"
include "eqbrtrrd.mm"
include "ex.mm"
include "hstle1.mm"
include "ad2ant2r.mm"
include "jctild.mm"
include "wb.mm"
include "chil.mm"
include "cr.mm"
include "hstcl.mm"
include "normcl.mm"
include "1re.mm"
include "letri3.mm"
include "mpan2.mm"
include "3syl.mm"
include "sylibrd.mm"

theorem hstles
  let cA: class A
  let cB: class B
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f


  assert |- ( ( ( S e. CHStates /\ A e. CH ) /\ ( B e. CH /\ A C_ B ) ) -> ( ( normh ` ( S ` A ) ) = 1 -> ( normh ` ( S ` B ) ) = 1 ) )

  proof
    cS
    chst
    wcel
    #
    cA
    cch
    wcel
    #
    wa
    cB
    cch
    wcel
    #
    cA
    cB
    wss
    #
    wa
    wa
    #
    cA
    cS
    cfv
    cno
    cfv
    #
    c1
    wceq
    #
    cB
    cS
    cfv
    #
    cno
    cfv
    #
    c1
    cle
    wbr
    #
    c1
    @8
    cle
    wbr
    #
    wa
    #
    @8
    c1
    wceq
    #
    @4
    @6
    @10
    @9
    @4
    @6
    @10
    @4
    @6
    wa
    @5
    c1
    @8
    cle
    @4
    @6
    simpr
    @4
    @5
    @8
    cle
    wbr
    @6
    cA
    cB
    cS
    hstle
    adantr
    eqbrtrrd
    ex
    @0
    @2
    @9
    @1
    @3
    cB
    cS
    hstle1
    ad2ant2r
    jctild
    @0
    @2
    @12
    @11
    wb
    #
    @1
    @3
    @0
    @2
    wa
    @7
    chil
    wcel
    @8
    cr
    wcel
    #
    @13
    cB
    cS
    hstcl
    @7
    normcl
    @14
    c1
    cr
    wcel
    @13
    1re
    @8
    c1
    letri3
    mpan2
    3syl
    ad2ant2r
    sylibrd
end
