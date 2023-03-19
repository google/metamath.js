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
include "csup.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "nfsup.mm"
include "nfel.mm"
include "nfan.mm"
include "adantr.mm"
include "wf.mm"
include "cle.mm"
include "wi.mm"
include "wral.mm"
include "simpr.mm"
include "pimdecfgtioc.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wn.mm"
include "cioo.mm"
include "iooborel.mm"
include "eqeltri.mm"
include "nfn.mm"
include "nfv.mm"
include "pimdecfgtioo.mm"
include "pm2.61dan.mm"

theorem decsmflem
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
  assume decsmflem.x: |- F/ x ph
  assume decsmflem.y: |- F/ y ph
  assume decsmflem.a: |- ( ph -> A C_ RR )
  assume decsmflem.f: |- ( ph -> F : A --> RR* )
  assume decsmflem.i: |- ( ph -> A. x e. A A. y e. A ( x <_ y -> ( F ` y ) <_ ( F ` x ) ) )
  assume decsmflem.j: |- J = ( topGen ` ran (,) )
  assume decsmflem.b: |- B = ( SalGen ` J )
  assume decsmflem.r: |- ( ph -> R e. RR* )
  assume decsmflem.l: |- Y = { x e. A | R < ( F ` x ) }
  assume decsmflem.c: |- C = sup ( Y , RR* , < )
  assume decsmflem.d: |- D = ( -oo (,) C )
  assume decsmflem.e: |- E = ( -oo (,] C )

  disjoint A b
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B b
  disjoint C y
  disjoint D b
  disjoint D x
  disjoint D y
  disjoint E b
  disjoint E x
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
    decsmflem.e
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
    cR
    vx
    cv
    #
    cF
    cfv
    #
    clt
    wbr
    #
    vx
    cA
    crab
    #
    cA
    decsmflem.l
    @10
    vx
    cA
    ssrab2
    eqsstri
    a1i
    decsmflem.a
    sstrd
    sselda
    decsmflem.j
    decsmflem.b
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
    decsmflem.x
    vx
    cC
    cY
    vx
    cC
    cY
    cxr
    clt
    csup
    decsmflem.c
    vx
    cY
    cxr
    clt
    vx
    cY
    @11
    decsmflem.l
    @10
    vx
    cA
    nfrab1
    nfcxfr
    #
    vx
    cxr
    nfcv
    vx
    clt
    nfcv
    nfsup
    nfcxfr
    @12
    nfel
    #
    nfan
    wph
    cA
    cr
    wss
    #
    @0
    decsmflem.a
    adantr
    wph
    cA
    cxr
    cF
    wf
    #
    @0
    decsmflem.f
    adantr
    wph
    @8
    vy
    cv
    #
    cle
    wbr
    @16
    cF
    cfv
    @9
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
    decsmflem.i
    adantr
    wph
    cR
    cxr
    wcel
    #
    @0
    decsmflem.r
    adantr
    decsmflem.l
    decsmflem.c
    wph
    @0
    simpr
    decsmflem.e
    pimdecfgtioc
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
    @21
    @19
    @21
    wph
    cD
    cmnf
    cC
    cioo
    co
    cB
    decsmflem.d
    cmnf
    cB
    cC
    cJ
    decsmflem.j
    decsmflem.b
    iooborel
    eqeltri
    a1i
    adantr
    @20
    vx
    vy
    cA
    cR
    cC
    cF
    cD
    cY
    wph
    @19
    vx
    decsmflem.x
    @0
    vx
    @13
    nfn
    nfan
    wph
    @19
    vy
    decsmflem.y
    @19
    vy
    nfv
    nfan
    wph
    @14
    @19
    decsmflem.a
    adantr
    wph
    @15
    @19
    decsmflem.f
    adantr
    wph
    @17
    @19
    decsmflem.i
    adantr
    wph
    @18
    @19
    decsmflem.r
    adantr
    decsmflem.l
    decsmflem.c
    wph
    @19
    simpr
    decsmflem.d
    pimdecfgtioo
    @3
    @23
    vb
    cD
    cB
    @1
    cD
    wceq
    @2
    @22
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
