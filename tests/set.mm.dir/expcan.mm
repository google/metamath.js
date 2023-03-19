include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "cexp.mm"
include "co.mm"
include "wb.mm"
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
include "ltexp2a.mm"
include "expr.mm"
include "syl31anc.mm"
include "eqord1.mm"
include "ancom2s.mm"
include "exp43.mm"
include "com24.mm"
include "3imp1.mm"
include "bicomd.mm"

theorem expcan
  let cA: class A
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( A e. RR /\ M e. ZZ /\ N e. ZZ ) /\ 1 < A ) -> ( ( A ^ M ) = ( A ^ N ) <-> M = N ) )

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
    w3a
    c1
    cA
    clt
    wbr
    #
    wa
    cM
    cN
    wceq
    #
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
    wceq
    #
    @0
    @1
    @2
    @3
    @4
    @7
    wb
    #
    @0
    @3
    @2
    @1
    @8
    @0
    @3
    @2
    @1
    @8
    @0
    @3
    wa
    #
    @1
    @2
    @8
    @9
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
    @5
    @6
    @10
    @12
    cA
    cexp
    oveq2
    @10
    cM
    cA
    cexp
    oveq2
    @10
    cN
    cA
    cexp
    oveq2
    zssre
    @9
    @10
    cz
    wcel
    #
    wa
    @11
    @9
    cA
    crp
    wcel
    @14
    @11
    crp
    wcel
    @9
    cA
    @0
    @3
    simpl
    #
    @9
    cc0
    c1
    cA
    @9
    0red
    @9
    1red
    @15
    cc0
    c1
    clt
    wbr
    @9
    0lt1
    a1i
    @0
    @3
    simpr
    lttrd
    elrpd
    cA
    @10
    rpexpcl
    sylan
    rpred
    @9
    @14
    @12
    cz
    wcel
    #
    wa
    #
    wa
    @0
    @14
    @16
    @3
    @10
    @12
    clt
    wbr
    #
    @11
    @13
    clt
    wbr
    #
    wi
    @0
    @3
    @17
    simpll
    @9
    @14
    @16
    simprl
    @9
    @14
    @16
    simprr
    @0
    @3
    @17
    simplr
    @0
    @14
    @16
    w3a
    @3
    @18
    @19
    cA
    @10
    @12
    ltexp2a
    expr
    syl31anc
    eqord1
    ancom2s
    exp43
    com24
    3imp1
    bicomd
end
