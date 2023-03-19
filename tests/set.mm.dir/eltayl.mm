include "cop.mm"
include "wcel.mm"
include "cc.mm"
include "cv.mm"
include "csn.mm"
include "ccnfld.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "cz.mm"
include "cin.mm"
include "cdvn.mm"
include "cfv.mm"
include "cfa.mm"
include "cdiv.mm"
include "cmin.mm"
include "cexp.mm"
include "cmul.mm"
include "cmpt.mm"
include "ctsu.mm"
include "cxp.mm"
include "ciun.mm"
include "wbr.mm"
include "wa.mm"
include "taylfval.mm"
include "eleq2d.mm"
include "df-br.mm"
include "bicomi.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "mpteq2dv.mm"
include "opeliunxp2.mm"
include "3bitr3g.mm"

theorem eltayl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let vk: setvar k
  let cF: class F
  let cN: class N
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vs: setvar s
  assume taylfval.s: |- ( ph -> S e. { RR , CC } )
  assume taylfval.f: |- ( ph -> F : A --> CC )
  assume taylfval.a: |- ( ph -> A C_ S )
  assume taylfval.n: |- ( ph -> ( N e. NN0 \/ N = +oo ) )
  assume taylfval.b: |- ( ( ph /\ k e. ( ( 0 [,] N ) i^i ZZ ) ) -> B e. dom ( ( S Dn F ) ` k ) )
  assume taylfval.t: |- T = ( N ( S Tayl F ) B )

  disjoint B k
  disjoint F k
  disjoint k ph
  disjoint N k
  disjoint S k
  disjoint X k
  disjoint a k
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint n x
  disjoint n y
  disjoint B n
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint a f
  disjoint a s
  disjoint F a
  disjoint f k
  disjoint f n
  disjoint f s
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint k s
  disjoint n s
  disjoint F n
  disjoint s x
  disjoint s y
  disjoint F s
  disjoint F x
  disjoint F y
  disjoint a ph
  disjoint f ph
  disjoint n ph
  disjoint ph s
  disjoint ph x
  disjoint ph y
  disjoint Y x
  disjoint N a
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint S a
  disjoint S f
  disjoint S n
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint T y
  disjoint X x
  assert |- ( ph -> ( X T Y <-> ( X e. CC /\ Y e. ( CCfld tsums ( k e. ( ( 0 [,] N ) i^i ZZ ) |-> ( ( ( ( ( S Dn F ) ` k ) ` B ) / ( ! ` k ) ) x. ( ( X - B ) ^ k ) ) ) ) ) ) )

  proof
    wph
    cX
    cY
    cop
    #
    cT
    wcel
    #
    @0
    vx
    cc
    vx
    cv
    #
    csn
    ccnfld
    vk
    cc0
    cN
    cicc
    co
    cz
    cin
    #
    cB
    vk
    cv
    #
    cS
    cF
    cdvn
    co
    cfv
    cfv
    @4
    cfa
    cfv
    cdiv
    co
    #
    @2
    cB
    cmin
    co
    #
    @4
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    ctsu
    co
    #
    cxp
    ciun
    #
    wcel
    cX
    cY
    cT
    wbr
    #
    cX
    cc
    wcel
    cY
    ccnfld
    vk
    @3
    @5
    cX
    cB
    cmin
    co
    #
    @4
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    ctsu
    co
    #
    wcel
    wa
    wph
    cT
    @11
    @0
    wph
    vx
    cA
    cB
    cS
    cT
    vk
    cF
    cN
    taylfval.s
    taylfval.f
    taylfval.a
    taylfval.n
    taylfval.b
    taylfval.t
    taylfval
    eleq2d
    @12
    @1
    cX
    cY
    cT
    df-br
    bicomi
    vx
    cc
    @10
    cX
    cY
    @17
    @2
    cX
    wceq
    #
    @9
    @16
    ccnfld
    ctsu
    @18
    vk
    @3
    @8
    @15
    @18
    @7
    @14
    @5
    cmul
    @18
    @6
    @13
    @4
    cexp
    @2
    cX
    cB
    cmin
    oveq1
    oveq1d
    oveq2d
    mpteq2dv
    oveq2d
    opeliunxp2
    3bitr3g
end
