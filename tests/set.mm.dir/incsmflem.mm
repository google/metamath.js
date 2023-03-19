include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "cmnf.mm"
include "cioc.mm"
include "co.mm"
include "cxr.mm"
include "mnfxr.mm"
include "a1i.mm"
include "cr.mm"
include "wss.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sstrd.mm"
include "sselda.mm"
include "iocborel.mm"
include "syl5eqel.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "nfel.mm"
include "nfan.mm"
include "nfv.mm"
include "adantr.mm"
include "wf.mm"
include "cle.mm"
include "wi.mm"
include "wral.mm"
include "simpr.mm"
include "pimincfltioc.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wn.mm"
include "cioo.mm"
include "iooborel.mm"
include "eqeltri.mm"
include "nfn.mm"
include "pimincfltioo.mm"
include "pm2.61dan.mm"

theorem incsmflem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cE: class E
  let cF: class F
  let cJ: class J
  let cY: class Y
  let vb: setvar b
  let vk: setvar k
  assume incsmflem.x: |- F/ x ph
  assume incsmflem.y: |- F/ y ph
  assume incsmflem.a: |- ( ph -> A C_ RR )
  assume incsmflem.f: |- ( ph -> F : A --> RR* )
  assume incsmflem.i: |- ( ph -> A. x e. A A. y e. A ( x <_ y -> ( F ` x ) <_ ( F ` y ) ) )
  assume incsmflem.j: |- J = ( topGen ` ran (,) )
  assume incsmflem.b: |- B = ( SalGen ` J )
  assume incsmflem.r: |- ( ph -> R e. RR* )
  assume incsmflem.l: |- Y = { x e. A | ( F ` x ) < R }
  assume incsmflem.c: |- C = sup ( Y , RR* , < )
  assume incsmflem.d: |- D = ( -oo (,) C )
  assume incsmflem.e: |- E = ( -oo (,] C )

  disjoint A b
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B b
  disjoint C x
  disjoint C y
  disjoint D b
  disjoint D x
  disjoint D y
  disjoint E b
  disjoint E x
  disjoint E y
  disjoint F x
  disjoint F y
  disjoint R x
  disjoint R y
  disjoint Y b
  disjoint Y y
  disjoint k x
  assert |- ( ph -> E. b e. B Y = ( b i^i A ) )

  proof
    wph
    cC
    cY
    wcel
    #
    cY
    vb
    cv
    #
    cA
    cin
    #
    wceq
    #
    vb
    cB
    wrex
    #
    wph
    @0
    wa
    #
    cE
    cB
    wcel
    cY
    cE
    cA
    cin
    #
    wceq
    #
    @4
    @5
    cE
    cmnf
    cC
    cioc
    co
    cB
    incsmflem.e
    @5
    cmnf
    cB
    cC
    cJ
    cmnf
    cxr
    wcel
    @5
    mnfxr
    a1i
    wph
    cY
    cr
    cC
    wph
    cY
    cA
    cr
    cY
    cA
    wss
    wph
    cY
    vx
    cv
    #
    cF
    cfv
    #
    cR
    clt
    wbr
    #
    vx
    cA
    crab
    #
    cA
    incsmflem.l
    @10
    vx
    cA
    ssrab2
    eqsstri
    a1i
    incsmflem.a
    sstrd
    sselda
    incsmflem.j
    incsmflem.b
    iocborel
    syl5eqel
    @5
    vx
    vy
    cA
    cR
    cC
    cF
    cE
    cY
    wph
    @0
    vx
    incsmflem.x
    vx
    cC
    cY
    vx
    cC
    nfcv
    vx
    cY
    @11
    incsmflem.l
    @10
    vx
    cA
    nfrab1
    nfcxfr
    nfel
    #
    nfan
    wph
    @0
    vy
    incsmflem.y
    @0
    vy
    nfv
    nfan
    wph
    cA
    cr
    wss
    #
    @0
    incsmflem.a
    adantr
    wph
    cA
    cxr
    cF
    wf
    #
    @0
    incsmflem.f
    adantr
    wph
    @8
    vy
    cv
    #
    cle
    wbr
    @9
    @15
    cF
    cfv
    cle
    wbr
    wi
    vy
    cA
    wral
    vx
    cA
    wral
    #
    @0
    incsmflem.i
    adantr
    wph
    cR
    cxr
    wcel
    #
    @0
    incsmflem.r
    adantr
    incsmflem.l
    incsmflem.c
    wph
    @0
    simpr
    incsmflem.e
    pimincfltioc
    @3
    @7
    vb
    cE
    cB
    @1
    cE
    wceq
    @2
    @6
    cY
    @1
    cE
    cA
    ineq1
    eqeq2d
    rspcev
    syl2anc
    wph
    @0
    wn
    #
    wa
    #
    cD
    cB
    wcel
    #
    cY
    cD
    cA
    cin
    #
    wceq
    #
    @4
    wph
    @20
    @18
    @20
    wph
    cD
    cmnf
    cC
    cioo
    co
    cB
    incsmflem.d
    cmnf
    cB
    cC
    cJ
    incsmflem.j
    incsmflem.b
    iooborel
    eqeltri
    a1i
    adantr
    @19
    vx
    vy
    cA
    cR
    cC
    cF
    cD
    cY
    wph
    @18
    vx
    incsmflem.x
    @0
    vx
    @12
    nfn
    nfan
    wph
    @18
    vy
    incsmflem.y
    @18
    vy
    nfv
    nfan
    wph
    @13
    @18
    incsmflem.a
    adantr
    wph
    @14
    @18
    incsmflem.f
    adantr
    wph
    @16
    @18
    incsmflem.i
    adantr
    wph
    @17
    @18
    incsmflem.r
    adantr
    incsmflem.l
    incsmflem.c
    wph
    @18
    simpr
    incsmflem.d
    pimincfltioo
    @3
    @22
    vb
    cD
    cB
    @1
    cD
    wceq
    @2
    @21
    cY
    @1
    cD
    cA
    ineq1
    eqeq2d
    rspcev
    syl2anc
    pm2.61dan
end
