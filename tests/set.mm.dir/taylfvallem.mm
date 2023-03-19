include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "cz.mm"
include "cin.mm"
include "cv.mm"
include "cdvn.mm"
include "cfv.mm"
include "cfa.mm"
include "cdiv.mm"
include "cmin.mm"
include "cexp.mm"
include "cmul.mm"
include "cmpt.mm"
include "ccnfld.mm"
include "cvv.mm"
include "cnfldbas.mm"
include "crg.mm"
include "ccmn.mm"
include "cnring.mm"
include "ringcmn.mm"
include "mp1i.mm"
include "ctps.mm"
include "cnfldtps.mm"
include "a1i.mm"
include "ovex.mm"
include "inex1.mm"
include "taylfvallem1.mm"
include "eqid.mm"
include "fmptd.mm"
include "tsmscl.mm"

theorem taylfvallem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cN: class N
  let cX: class X
  let va: setvar a
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vs: setvar s
  let cY: class Y
  let cT: class T
  assume taylfval.s: |- ( ph -> S e. { RR , CC } )
  assume taylfval.f: |- ( ph -> F : A --> CC )
  assume taylfval.a: |- ( ph -> A C_ S )
  assume taylfval.n: |- ( ph -> ( N e. NN0 \/ N = +oo ) )
  assume taylfval.b: |- ( ( ph /\ k e. ( ( 0 [,] N ) i^i ZZ ) ) -> B e. dom ( ( S Dn F ) ` k ) )

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
  assert |- ( ( ph /\ X e. CC ) -> ( CCfld tsums ( k e. ( ( 0 [,] N ) i^i ZZ ) |-> ( ( ( ( ( S Dn F ) ` k ) ` B ) / ( ! ` k ) ) x. ( ( X - B ) ^ k ) ) ) ) C_ CC )

  proof
    wph
    cX
    cc
    wcel
    wa
    #
    cc0
    cN
    cicc
    co
    #
    cz
    cin
    #
    cc
    vk
    @2
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
    @3
    cfa
    cfv
    cdiv
    co
    cX
    cB
    cmin
    co
    @3
    cexp
    co
    cmul
    co
    #
    cmpt
    #
    ccnfld
    cvv
    cnfldbas
    ccnfld
    crg
    wcel
    ccnfld
    ccmn
    wcel
    @0
    cnring
    ccnfld
    ringcmn
    mp1i
    ccnfld
    ctps
    wcel
    @0
    cnfldtps
    a1i
    @2
    cvv
    wcel
    @0
    @1
    cz
    cc0
    cN
    cicc
    ovex
    inex1
    a1i
    @0
    vk
    @2
    @4
    cc
    @5
    wph
    cA
    cB
    cS
    vk
    cF
    cN
    cX
    taylfval.s
    taylfval.f
    taylfval.a
    taylfval.n
    taylfval.b
    taylfvallem1
    @5
    eqid
    fmptd
    tsmscl
end
