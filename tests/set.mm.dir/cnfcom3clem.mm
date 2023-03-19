include "con0.mm"
include "wcel.mm"
include "com.mm"
include "cv.mm"
include "wss.mm"
include "coe.mm"
include "co.mm"
include "cfv.mm"
include "wf1o.mm"
include "c1o.mm"
include "cdif.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "w3a.mm"
include "simp1.mm"
include "c2o.mm"
include "omelon.mm"
include "1onn.mm"
include "ondif2.mm"
include "mpbir2an.mm"
include "oeworde.mm"
include "sylancr.mm"
include "simp2.mm"
include "sseldd.mm"
include "simp3.mm"
include "cnfcom3lem.mm"
include "cnfcom3.mm"
include "wceq.mm"
include "wb.mm"
include "cvv.mm"
include "wf.mm"
include "f1of.mm"
include "syl.mm"
include "vex.mm"
include "fex.mm"
include "sylancl.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "f1oeq1.mm"
include "mpbird.mm"
include "oveq2.mm"
include "f1oeq3.mm"
include "rspcev.mm"
include "3expia.mm"
include "ralrimiva.mm"
include "cmpt.mm"
include "ovex.mm"
include "mptex.mm"
include "eqeltri.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfeq2.mm"
include "fveq1.mm"
include "rexbidv.mm"
include "imbi2d.mm"
include "ralbid.mm"
include "spcev.mm"

theorem cnfcom3clem
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vb: setvar b
  assume cnfcom3c.s: |- S = dom ( _om CNF A )
  assume cnfcom3c.f: |- F = ( `' ( _om CNF A ) ` b )
  assume cnfcom3c.g: |- G = OrdIso ( _E , ( F supp (/) ) )
  assume cnfcom3c.h: |- H = seqom ( ( k e. _V , z e. _V |-> ( M +o z ) ) , (/) )
  assume cnfcom3c.t: |- T = seqom ( ( k e. _V , f e. _V |-> K ) , (/) )
  assume cnfcom3c.m: |- M = ( ( _om ^o ( G ` k ) ) .o ( F ` ( G ` k ) ) )
  assume cnfcom3c.k: |- K = ( ( x e. M |-> ( dom f +o x ) ) u. `' ( x e. dom f |-> ( M +o x ) ) )
  assume cnfcom3c.w: |- W = ( G ` U. dom G )
  assume cnfcom3c.x: |- X = ( u e. ( F ` W ) , v e. ( _om ^o W ) |-> ( ( ( F ` W ) .o v ) +o u ) )
  assume cnfcom3c.y: |- Y = ( u e. ( F ` W ) , v e. ( _om ^o W ) |-> ( ( ( _om ^o W ) .o u ) +o v ) )
  assume cnfcom3c.n: |- N = ( ( X o. `' Y ) o. ( T ` dom G ) )
  assume cnfcom3c.l: |- L = ( b e. ( _om ^o A ) |-> N )

  disjoint b g
  disjoint b k
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b z
  disjoint A b
  disjoint g k
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g z
  disjoint A g
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k z
  disjoint A k
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint K u
  disjoint K v
  disjoint L g
  disjoint L w
  disjoint M x
  disjoint T u
  disjoint T v
  disjoint T z
  disjoint f k
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f z
  disjoint F f
  disjoint F k
  disjoint F u
  disjoint F v
  disjoint F x
  disjoint F z
  disjoint G f
  disjoint G k
  disjoint G u
  disjoint G v
  disjoint G x
  disjoint G z
  disjoint H f
  disjoint H u
  disjoint H v
  disjoint H x
  disjoint S k
  disjoint S z
  disjoint W u
  disjoint W v
  disjoint W w
  disjoint W x
  assert |- ( A e. On -> E. g A. b e. A ( _om C_ b -> E. w e. ( On \ 1o ) ( g ` b ) : b -1-1-onto-> ( _om ^o w ) ) )

  proof
    cA
    con0
    wcel
    #
    com
    vb
    cv
    #
    wss
    #
    @1
    com
    vw
    cv
    #
    coe
    co
    #
    @1
    cL
    cfv
    #
    wf1o
    #
    vw
    con0
    c1o
    cdif
    #
    wrex
    #
    wi
    #
    vb
    cA
    wral
    #
    @2
    @1
    @4
    @1
    vg
    cv
    #
    cfv
    #
    wf1o
    #
    vw
    @7
    wrex
    #
    wi
    #
    vb
    cA
    wral
    #
    vg
    wex
    @0
    @9
    vb
    cA
    @0
    @1
    cA
    wcel
    #
    @2
    @8
    @0
    @17
    @2
    w3a
    #
    cW
    @7
    wcel
    @1
    com
    cW
    coe
    co
    #
    @5
    wf1o
    #
    @8
    @18
    vx
    vz
    cA
    @1
    cS
    cT
    vf
    vk
    cF
    cG
    cH
    cK
    cM
    cW
    cnfcom3c.s
    @0
    @17
    @2
    simp1
    #
    @18
    cA
    com
    cA
    coe
    co
    #
    @1
    @18
    com
    con0
    c2o
    cdif
    wcel
    #
    @0
    cA
    @22
    wss
    @23
    com
    con0
    wcel
    c1o
    com
    wcel
    omelon
    1onn
    com
    ondif2
    mpbir2an
    @21
    com
    cA
    oeworde
    sylancr
    @0
    @17
    @2
    simp2
    sseldd
    #
    cnfcom3c.f
    cnfcom3c.g
    cnfcom3c.h
    cnfcom3c.t
    cnfcom3c.m
    cnfcom3c.k
    cnfcom3c.w
    @0
    @17
    @2
    simp3
    #
    cnfcom3lem
    @18
    @20
    @1
    @19
    cN
    wf1o
    #
    @18
    vx
    vz
    vv
    vu
    cA
    @1
    cS
    cT
    vf
    vk
    cF
    cG
    cH
    cK
    cM
    cN
    cW
    cX
    cY
    cnfcom3c.s
    @21
    @24
    cnfcom3c.f
    cnfcom3c.g
    cnfcom3c.h
    cnfcom3c.t
    cnfcom3c.m
    cnfcom3c.k
    cnfcom3c.w
    @25
    cnfcom3c.x
    cnfcom3c.y
    cnfcom3c.n
    cnfcom3
    #
    @18
    @5
    cN
    wceq
    #
    @20
    @26
    wb
    @18
    @1
    @22
    wcel
    cN
    cvv
    wcel
    #
    @28
    @24
    @18
    @1
    @19
    cN
    wf
    #
    @1
    cvv
    wcel
    @29
    @18
    @26
    @30
    @27
    @1
    @19
    cN
    f1of
    syl
    vb
    vex
    @1
    @19
    cvv
    cN
    fex
    sylancl
    vb
    @22
    cN
    cvv
    cL
    cnfcom3c.l
    fvmpt2
    syl2anc
    @1
    @19
    @5
    cN
    f1oeq1
    syl
    mpbird
    @6
    @20
    vw
    cW
    @7
    @3
    cW
    wceq
    @4
    @19
    wceq
    @6
    @20
    wb
    @3
    cW
    com
    coe
    oveq2
    @4
    @19
    @1
    @5
    f1oeq3
    syl
    rspcev
    syl2anc
    3expia
    ralrimiva
    @16
    @10
    vg
    cL
    cL
    vb
    @22
    cN
    cmpt
    #
    cvv
    cnfcom3c.l
    vb
    @22
    cN
    com
    cA
    coe
    ovex
    mptex
    eqeltri
    @11
    cL
    wceq
    #
    @15
    @9
    vb
    cA
    vb
    @11
    cL
    vb
    cL
    @31
    cnfcom3c.l
    vb
    @22
    cN
    nfmpt1
    nfcxfr
    nfeq2
    @32
    @14
    @8
    @2
    @32
    @13
    @6
    vw
    @7
    @32
    @12
    @5
    wceq
    @13
    @6
    wb
    @1
    @11
    cL
    fveq1
    @1
    @4
    @12
    @5
    f1oeq1
    syl
    rexbidv
    imbi2d
    ralbid
    spcev
    syl
end
