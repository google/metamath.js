include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "com.mm"
include "cv.mm"
include "wss.mm"
include "cxp.mm"
include "cfv.mm"
include "wf1o.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "con0.mm"
include "mptexg.mm"
include "syl.mm"
include "wa.mm"
include "adantr.mm"
include "simprl.mm"
include "onelon.mm"
include "syl2anc.mm"
include "simprr.mm"
include "c1o.mm"
include "cdif.mm"
include "coe.mm"
include "co.mm"
include "infxpenc2lem1.mm"
include "simpld.mm"
include "c2o.mm"
include "c0.mm"
include "wceq.mm"
include "simprd.mm"
include "infxpenc.mm"
include "wb.mm"
include "wf.mm"
include "f1of.mm"
include "vex.mm"
include "xpex.mm"
include "fex.mm"
include "sylancl.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "f1oeq1.mm"
include "mpbird.mm"
include "expr.mm"
include "ralrimiva.mm"
include "nfmpt1.mm"
include "nfeq2.mm"
include "fveq1.mm"
include "imbi2d.mm"
include "ralbid.mm"
include "spcegv.mm"
include "sylc.mm"

theorem infxpenc2lem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cT: class T
  let vg: setvar g
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vb: setvar b
  assume infxpenc2.1: |- ( ph -> A e. On )
  assume infxpenc2.2: |- ( ph -> A. b e. A ( _om C_ b -> E. w e. ( On \ 1o ) ( n ` b ) : b -1-1-onto-> ( _om ^o w ) ) )
  assume infxpenc2.3: |- W = ( `' ( x e. ( On \ 1o ) |-> ( _om ^o x ) ) ` ran ( n ` b ) )
  assume infxpenc2.4: |- ( ph -> F : ( _om ^o 2o ) -1-1-onto-> _om )
  assume infxpenc2.5: |- ( ph -> ( F ` (/) ) = (/) )
  assume infxpenc2.k: |- K = ( y e. { x e. ( ( _om ^o 2o ) ^m W ) | x finSupp (/) } |-> ( F o. ( y o. `' ( _I |` W ) ) ) )
  assume infxpenc2.h: |- H = ( ( ( _om CNF W ) o. K ) o. `' ( ( _om ^o 2o ) CNF W ) )
  assume infxpenc2.l: |- L = ( y e. { x e. ( _om ^m ( W .o 2o ) ) | x finSupp (/) } |-> ( ( _I |` _om ) o. ( y o. `' ( Y o. `' X ) ) ) )
  assume infxpenc2.x: |- X = ( z e. 2o , w e. W |-> ( ( W .o z ) +o w ) )
  assume infxpenc2.y: |- Y = ( z e. 2o , w e. W |-> ( ( 2o .o w ) +o z ) )
  assume infxpenc2.j: |- J = ( ( ( _om CNF ( 2o .o W ) ) o. L ) o. `' ( _om CNF ( W .o 2o ) ) )
  assume infxpenc2.z: |- Z = ( x e. ( _om ^o W ) , y e. ( _om ^o W ) |-> ( ( ( _om ^o W ) .o x ) +o y ) )
  assume infxpenc2.t: |- T = ( x e. b , y e. b |-> <. ( ( n ` b ) ` x ) , ( ( n ` b ) ` y ) >. )
  assume infxpenc2.g: |- G = ( `' ( n ` b ) o. ( ( ( H o. J ) o. Z ) o. T ) )

  disjoint b g
  disjoint b n
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint A b
  disjoint g n
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint b ph
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint g z
  disjoint W g
  disjoint w z
  disjoint W w
  disjoint x z
  disjoint W x
  disjoint y z
  disjoint W y
  disjoint W z
  disjoint F g
  disjoint F x
  disjoint F y
  disjoint G g
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> E. g A. b e. A ( _om C_ b -> ( g ` b ) : ( b X. b ) -1-1-onto-> b ) )

  proof
    wph
    vb
    cA
    cG
    cmpt
    #
    cvv
    wcel
    #
    com
    vb
    cv
    #
    wss
    #
    @2
    @2
    cxp
    #
    @2
    @2
    @0
    cfv
    #
    wf1o
    #
    wi
    #
    vb
    cA
    wral
    #
    @3
    @4
    @2
    @2
    vg
    cv
    #
    cfv
    #
    wf1o
    #
    wi
    #
    vb
    cA
    wral
    #
    vg
    wex
    wph
    cA
    con0
    wcel
    #
    @1
    infxpenc2.1
    vb
    cA
    cG
    con0
    mptexg
    syl
    wph
    @7
    vb
    cA
    wph
    @2
    cA
    wcel
    #
    @3
    @6
    wph
    @15
    @3
    wa
    #
    wa
    #
    @6
    @4
    @2
    cG
    wf1o
    #
    @17
    vx
    vy
    vz
    vw
    @2
    cT
    cF
    cG
    cH
    cJ
    cK
    cL
    @2
    vn
    cv
    cfv
    #
    cW
    cX
    cY
    cZ
    @17
    @14
    @15
    @2
    con0
    wcel
    wph
    @14
    @16
    infxpenc2.1
    adantr
    wph
    @15
    @3
    simprl
    #
    cA
    @2
    onelon
    syl2anc
    wph
    @15
    @3
    simprr
    @17
    cW
    con0
    c1o
    cdif
    wcel
    #
    @2
    com
    cW
    coe
    co
    @19
    wf1o
    #
    wph
    vx
    vw
    cA
    vn
    cW
    vb
    infxpenc2.1
    infxpenc2.2
    infxpenc2.3
    infxpenc2lem1
    #
    simpld
    wph
    com
    c2o
    coe
    co
    com
    cF
    wf1o
    @16
    infxpenc2.4
    adantr
    wph
    c0
    cF
    cfv
    c0
    wceq
    @16
    infxpenc2.5
    adantr
    @17
    @21
    @22
    @23
    simprd
    infxpenc2.k
    infxpenc2.h
    infxpenc2.l
    infxpenc2.x
    infxpenc2.y
    infxpenc2.j
    infxpenc2.z
    infxpenc2.t
    infxpenc2.g
    infxpenc
    #
    @17
    @5
    cG
    wceq
    #
    @6
    @18
    wb
    @17
    @15
    cG
    cvv
    wcel
    #
    @25
    @20
    @17
    @4
    @2
    cG
    wf
    #
    @4
    cvv
    wcel
    @26
    @17
    @18
    @27
    @24
    @4
    @2
    cG
    f1of
    syl
    @2
    @2
    vb
    vex
    #
    @28
    xpex
    @4
    @2
    cvv
    cG
    fex
    sylancl
    vb
    cA
    cG
    cvv
    @0
    @0
    eqid
    fvmpt2
    syl2anc
    @4
    @2
    @5
    cG
    f1oeq1
    syl
    mpbird
    expr
    ralrimiva
    @13
    @8
    vg
    @0
    cvv
    @9
    @0
    wceq
    #
    @12
    @7
    vb
    cA
    vb
    @9
    @0
    vb
    cA
    cG
    nfmpt1
    nfeq2
    @29
    @11
    @6
    @3
    @29
    @10
    @5
    wceq
    @11
    @6
    wb
    @2
    @9
    @0
    fveq1
    @4
    @2
    @10
    @5
    f1oeq1
    syl
    imbi2d
    ralbid
    spcegv
    sylc
end
