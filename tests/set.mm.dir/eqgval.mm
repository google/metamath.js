include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "wbr.mm"
include "cv.mm"
include "cpr.mm"
include "cfv.mm"
include "co.mm"
include "copab.mm"
include "w3a.mm"
include "eqgfval.mm"
include "breqd.mm"
include "cvv.mm"
include "brabv.mm"
include "adantl.mm"
include "simpr1.mm"
include "elex.mm"
include "syl.mm"
include "simpr2.mm"
include "jca.mm"
include "wceq.mm"
include "vex.mm"
include "prss.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "syl5bbr.mm"
include "fveq2.mm"
include "id.mm"
include "oveqan12d.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "df-3an.mm"
include "syl6bbr.mm"
include "eqid.mm"
include "brabga.mm"
include "pm5.21nd.mm"
include "bitrd.mm"

theorem eqgval
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  let vs: setvar s
  assume eqgval.x: |- X = ( Base ` G )
  assume eqgval.n: |- N = ( invg ` G )
  assume eqgval.p: |- .+ = ( +g ` G )
  assume eqgval.r: |- R = ( G ~QG S )


  assert |- ( ( G e. V /\ S C_ X ) -> ( A R B <-> ( A e. X /\ B e. X /\ ( ( N ` A ) .+ B ) e. S ) ) )

  proof
    cG
    cV
    wcel
    cS
    cX
    wss
    wa
    #
    cA
    cB
    cR
    wbr
    cA
    cB
    vx
    cv
    #
    vy
    cv
    #
    cpr
    cX
    wss
    #
    @1
    cN
    cfv
    #
    @2
    c.pl
    co
    #
    cS
    wcel
    #
    wa
    #
    vx
    vy
    copab
    #
    wbr
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cA
    cN
    cfv
    #
    cB
    c.pl
    co
    #
    cS
    wcel
    #
    w3a
    #
    @0
    cR
    @8
    cA
    cB
    vx
    vy
    c.pl
    cR
    cS
    cG
    cN
    cV
    cX
    eqgval.x
    eqgval.n
    eqgval.p
    eqgval.r
    eqgfval
    breqd
    @0
    @9
    @15
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    #
    @9
    @18
    @0
    @7
    vx
    vy
    cA
    cB
    brabv
    adantl
    @0
    @15
    wa
    #
    @16
    @17
    @19
    @10
    @16
    @0
    @10
    @11
    @14
    simpr1
    cA
    cX
    elex
    syl
    @19
    @11
    @17
    @0
    @10
    @11
    @14
    simpr2
    cB
    cX
    elex
    syl
    jca
    @7
    @15
    vx
    vy
    cA
    cB
    @8
    cvv
    cvv
    @1
    cA
    wceq
    #
    @2
    cB
    wceq
    #
    wa
    #
    @7
    @10
    @11
    wa
    #
    @14
    wa
    @15
    @22
    @3
    @23
    @6
    @14
    @3
    @1
    cX
    wcel
    #
    @2
    cX
    wcel
    #
    wa
    @22
    @23
    @1
    @2
    cX
    vx
    vex
    vy
    vex
    prss
    @20
    @24
    @10
    @21
    @25
    @11
    @1
    cA
    cX
    eleq1
    @2
    cB
    cX
    eleq1
    bi2anan9
    syl5bbr
    @22
    @5
    @13
    cS
    @20
    @21
    @4
    @12
    @2
    cB
    c.pl
    @1
    cA
    cN
    fveq2
    @21
    id
    oveqan12d
    eleq1d
    anbi12d
    @10
    @11
    @14
    df-3an
    syl6bbr
    @8
    eqid
    brabga
    pm5.21nd
    bitrd
end
