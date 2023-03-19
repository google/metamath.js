include "wcel.mm"
include "cfbas.mm"
include "cfv.mm"
include "wf.mm"
include "w3a.mm"
include "cfm.mm"
include "co.mm"
include "wss.mm"
include "cv.mm"
include "cima.mm"
include "wrex.mm"
include "wa.mm"
include "elfm.mm"
include "cfg.mm"
include "ssfg.mm"
include "syl6sseqr.mm"
include "sselda.mm"
include "adantrr.mm"
include "3ad2antl2.mm"
include "simprr.mm"
include "weq.mm"
include "imaeq2.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexlimdvaa.mm"
include "wi.mm"
include "wb.mm"
include "eleq2i.mm"
include "elfg.mm"
include "syl5bb.mm"
include "3ad2ant2.mm"
include "imass2.mm"
include "sstr2.mm"
include "com12.mm"
include "ad2antll.mm"
include "syl5.mm"
include "reximdv.mm"
include "expr.mm"
include "com23.mm"
include "expimpd.mm"
include "sylbid.mm"
include "rexlimdv.mm"
include "impbid.mm"
include "anbi2d.mm"
include "bitrd.mm"

theorem elfm2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cL: class L
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vt: setvar t
  let vy: setvar y
  let vz: setvar z
  assume elfm2.l: |- L = ( Y filGen B )

  disjoint B x
  disjoint C x
  disjoint F x
  disjoint X x
  disjoint A x
  disjoint L x
  disjoint Y x
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint B s
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C s
  disjoint C t
  disjoint C y
  disjoint F s
  disjoint F t
  disjoint F y
  disjoint X s
  disjoint X t
  disjoint X y
  disjoint A y
  disjoint L s
  disjoint L y
  disjoint Y s
  disjoint Y t
  disjoint Y y
  assert |- ( ( X e. C /\ B e. ( fBas ` Y ) /\ F : Y --> X ) -> ( A e. ( ( X FilMap F ) ` B ) <-> ( A C_ X /\ E. x e. L ( F " x ) C_ A ) ) )

  proof
    cX
    cC
    wcel
    #
    cB
    cY
    cfbas
    cfv
    wcel
    #
    cY
    cX
    cF
    wf
    #
    w3a
    #
    cA
    cB
    cX
    cF
    cfm
    co
    cfv
    wcel
    cA
    cX
    wss
    #
    cF
    vy
    cv
    #
    cima
    #
    cA
    wss
    #
    vy
    cB
    wrex
    #
    wa
    @4
    cF
    vx
    cv
    #
    cima
    #
    cA
    wss
    #
    vx
    cL
    wrex
    #
    wa
    vy
    cA
    cB
    cC
    cF
    cX
    cY
    elfm
    @3
    @8
    @12
    @4
    @3
    @8
    @12
    @3
    @7
    @12
    vy
    cB
    @3
    @5
    cB
    wcel
    #
    @7
    wa
    #
    wa
    @5
    cL
    wcel
    #
    @7
    @12
    @1
    @0
    @14
    @15
    @2
    @1
    @13
    @15
    @7
    @1
    cB
    cL
    @5
    @1
    cB
    cY
    cB
    cfg
    co
    #
    cL
    cB
    cY
    ssfg
    elfm2.l
    syl6sseqr
    sselda
    adantrr
    3ad2antl2
    @3
    @13
    @7
    simprr
    @11
    @7
    vx
    @5
    cL
    vx
    vy
    weq
    @10
    @6
    cA
    @9
    @5
    cF
    imaeq2
    sseq1d
    rspcev
    syl2anc
    rexlimdvaa
    @3
    @11
    @8
    vx
    cL
    @3
    @9
    cL
    wcel
    #
    @9
    cY
    wss
    #
    @5
    @9
    wss
    #
    vy
    cB
    wrex
    #
    wa
    #
    @11
    @8
    wi
    #
    @1
    @0
    @17
    @21
    wb
    @2
    @17
    @9
    @16
    wcel
    @1
    @21
    cL
    @16
    @9
    elfm2.l
    eleq2i
    vy
    @9
    cB
    cY
    elfg
    syl5bb
    3ad2ant2
    @3
    @18
    @20
    @22
    @3
    @18
    wa
    @11
    @20
    @8
    @3
    @18
    @11
    @20
    @8
    wi
    @3
    @18
    @11
    wa
    wa
    #
    @19
    @7
    vy
    cB
    @19
    @6
    @10
    wss
    #
    @23
    @7
    @5
    @9
    cF
    imass2
    @11
    @24
    @7
    wi
    @3
    @18
    @24
    @11
    @7
    @6
    @10
    cA
    sstr2
    com12
    ad2antll
    syl5
    reximdv
    expr
    com23
    expimpd
    sylbid
    rexlimdv
    impbid
    anbi2d
    bitrd
end
