include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "cen.mm"
include "wbr.mm"
include "c1o.mm"
include "wa.mm"
include "cin.mm"
include "wceq.mm"
include "cv.mm"
include "wex.mm"
include "0ex.mm"
include "xpsnen.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "pm3.2i.mm"
include "xp01disj.mm"
include "p0ex.mm"
include "xpex.mm"
include "snex.mm"
include "breq1.mm"
include "bi2anan9.mm"
include "ineq12.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "spc2ev.mm"
include "mp2an.mm"

theorem endisj
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume endisj.1: |- A e. _V
  assume endisj.2: |- B e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- E. x E. y ( ( x ~~ A /\ y ~~ B ) /\ ( x i^i y ) = (/) )

  proof
    cA
    c0
    csn
    #
    cxp
    #
    cA
    cen
    wbr
    #
    cB
    c1o
    csn
    #
    cxp
    #
    cB
    cen
    wbr
    #
    wa
    #
    @1
    @4
    cin
    #
    c0
    wceq
    #
    vx
    cv
    #
    cA
    cen
    wbr
    #
    vy
    cv
    #
    cB
    cen
    wbr
    #
    wa
    #
    @9
    @11
    cin
    #
    c0
    wceq
    #
    wa
    #
    vy
    wex
    vx
    wex
    @2
    @5
    cA
    c0
    endisj.1
    0ex
    xpsnen
    cB
    c1o
    endisj.2
    c1o
    con0
    1on
    elexi
    xpsnen
    pm3.2i
    cA
    cB
    xp01disj
    @16
    @6
    @8
    wa
    vx
    vy
    @1
    @4
    cA
    @0
    endisj.1
    p0ex
    xpex
    cB
    @3
    endisj.2
    c1o
    snex
    xpex
    @9
    @1
    wceq
    #
    @11
    @4
    wceq
    #
    wa
    #
    @13
    @6
    @15
    @8
    @17
    @10
    @2
    @18
    @12
    @5
    @9
    @1
    cA
    cen
    breq1
    @11
    @4
    cB
    cen
    breq1
    bi2anan9
    @19
    @14
    @7
    c0
    @9
    @1
    @11
    @4
    ineq12
    eqeq1d
    anbi12d
    spc2ev
    mp2an
end
