include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cexp.mm"
include "co.mm"
include "wb.mm"
include "wa.mm"
include "cv.mm"
include "oveq2.mm"
include "zssre.mm"
include "crp.mm"
include "simpl.mm"
include "cc0.mm"
include "0red.mm"
include "1red.mm"
include "0lt1.mm"
include "a1i.mm"
include "simpr.mm"
include "lttrd.mm"
include "elrpd.mm"
include "rpexpcl.mm"
include "sylan.mm"
include "rpred.mm"
include "wi.mm"
include "simpll.mm"
include "simprl.mm"
include "simprr.mm"
include "simplr.mm"
include "w3a.mm"
include "ltexp2a.mm"
include "expr.mm"
include "syl31anc.mm"
include "ltord1.mm"
include "ancom2s.mm"
include "exp43.mm"
include "com24.mm"
include "3imp1.mm"

theorem ltexp2
  let cA: class A
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( A e. RR /\ M e. ZZ /\ N e. ZZ ) /\ 1 < A ) -> ( M < N <-> ( A ^ M ) < ( A ^ N ) ) )

  proof
    cA
    cr
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    c1
    cA
    clt
    wbr
    #
    cM
    cN
    clt
    wbr
    cA
    cM
    cexp
    co
    #
    cA
    cN
    cexp
    co
    #
    clt
    wbr
    wb
    #
    @0
    @3
    @2
    @1
    @6
    @0
    @3
    @2
    @1
    @6
    @0
    @3
    wa
    #
    @1
    @2
    @6
    @7
    vx
    vy
    cA
    vx
    cv
    #
    cexp
    co
    #
    cA
    vy
    cv
    #
    cexp
    co
    #
    cM
    cN
    cz
    @4
    @5
    @8
    @10
    cA
    cexp
    oveq2
    @8
    cM
    cA
    cexp
    oveq2
    @8
    cN
    cA
    cexp
    oveq2
    zssre
    @7
    @8
    cz
    wcel
    #
    wa
    @9
    @7
    cA
    crp
    wcel
    @12
    @9
    crp
    wcel
    @7
    cA
    @0
    @3
    simpl
    #
    @7
    cc0
    c1
    cA
    @7
    0red
    @7
    1red
    @13
    cc0
    c1
    clt
    wbr
    @7
    0lt1
    a1i
    @0
    @3
    simpr
    lttrd
    elrpd
    cA
    @8
    rpexpcl
    sylan
    rpred
    @7
    @12
    @10
    cz
    wcel
    #
    wa
    #
    wa
    @0
    @12
    @14
    @3
    @8
    @10
    clt
    wbr
    #
    @9
    @11
    clt
    wbr
    #
    wi
    @0
    @3
    @15
    simpll
    @7
    @12
    @14
    simprl
    @7
    @12
    @14
    simprr
    @0
    @3
    @15
    simplr
    @0
    @12
    @14
    w3a
    @3
    @16
    @17
    cA
    @8
    @10
    ltexp2a
    expr
    syl31anc
    ltord1
    ancom2s
    exp43
    com24
    3imp1
end
