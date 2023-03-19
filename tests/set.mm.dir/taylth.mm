include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "reelprrecn.mm"
include "a1i.mm"
include "wf.mm"
include "wss.mm"
include "ax-resscn.mm"
include "fss.mm"
include "sylancl.mm"
include "cv.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cmin.mm"
include "cdvn.mm"
include "cfv.mm"
include "cexp.mm"
include "cdiv.mm"
include "cmpt.mm"
include "climc.mm"
include "wa.mm"
include "adantr.mm"
include "cdm.mm"
include "wceq.mm"
include "cn.mm"
include "simprl.mm"
include "simprr.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "cbvmptv.mm"
include "oveq1i.mm"
include "syl6eleq.mm"
include "taylthlem2.mm"
include "taylthlem1.mm"

theorem taylth
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cT: class T
  let cF: class F
  let cN: class N
  let vm: setvar m
  let vy: setvar y
  let vk: setvar k
  let cM: class M
  assume taylth.f: |- ( ph -> F : A --> RR )
  assume taylth.a: |- ( ph -> A C_ RR )
  assume taylth.d: |- ( ph -> dom ( ( RR Dn F ) ` N ) = A )
  assume taylth.n: |- ( ph -> N e. NN )
  assume taylth.b: |- ( ph -> B e. A )
  assume taylth.t: |- T = ( N ( RR Tayl F ) B )
  assume taylth.r: |- R = ( x e. ( A \ { B } ) |-> ( ( ( F ` x ) - ( T ` x ) ) / ( ( x - B ) ^ N ) ) )

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint T x
  disjoint N x
  disjoint ph x
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint x y
  disjoint A y
  disjoint k m
  disjoint k x
  disjoint k y
  disjoint B k
  disjoint B m
  disjoint B y
  disjoint F k
  disjoint F m
  disjoint F y
  disjoint M x
  disjoint M y
  disjoint T m
  disjoint T y
  disjoint N k
  disjoint N m
  disjoint N y
  disjoint k ph
  disjoint m ph
  disjoint ph y
  assert |- ( ph -> 0 e. ( R limCC B ) )

  proof
    wph
    vx
    vy
    cA
    cB
    cR
    cr
    cT
    vm
    cF
    cN
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    wph
    cA
    cr
    cF
    wf
    #
    cr
    cc
    wss
    cA
    cc
    cF
    wf
    taylth.f
    ax-resscn
    cA
    cr
    cc
    cF
    fss
    sylancl
    taylth.a
    taylth.d
    taylth.n
    taylth.b
    taylth.t
    taylth.r
    wph
    vm
    cv
    #
    c1
    cN
    cfzo
    co
    wcel
    #
    cc0
    vy
    cA
    cB
    csn
    cdif
    #
    vy
    cv
    #
    cN
    @1
    cmin
    co
    #
    cr
    cF
    cdvn
    co
    #
    cfv
    #
    cfv
    #
    @4
    @5
    cc
    cT
    cdvn
    co
    cfv
    #
    cfv
    #
    cmin
    co
    #
    @4
    cB
    cmin
    co
    #
    @1
    cexp
    co
    #
    cdiv
    co
    #
    cmpt
    #
    cB
    climc
    co
    #
    wcel
    #
    wa
    #
    wa
    #
    vx
    cA
    cB
    cT
    cF
    @1
    cN
    wph
    @0
    @18
    taylth.f
    adantr
    wph
    cA
    cr
    wss
    @18
    taylth.a
    adantr
    wph
    cN
    @6
    cfv
    cdm
    cA
    wceq
    @18
    taylth.d
    adantr
    wph
    cN
    cn
    wcel
    @18
    taylth.n
    adantr
    wph
    cB
    cA
    wcel
    @18
    taylth.b
    adantr
    taylth.t
    wph
    @2
    @17
    simprl
    @19
    cc0
    @16
    vx
    @3
    vx
    cv
    #
    @7
    cfv
    #
    @20
    @9
    cfv
    #
    cmin
    co
    #
    @20
    cB
    cmin
    co
    #
    @1
    cexp
    co
    #
    cdiv
    co
    #
    cmpt
    #
    cB
    climc
    co
    wph
    @2
    @17
    simprr
    @15
    @27
    cB
    climc
    vy
    vx
    @3
    @14
    @26
    @4
    @20
    wceq
    #
    @11
    @23
    @13
    @25
    cdiv
    @28
    @8
    @21
    @10
    @22
    cmin
    @4
    @20
    @7
    fveq2
    @4
    @20
    @9
    fveq2
    oveq12d
    @28
    @12
    @24
    @1
    cexp
    @4
    @20
    cB
    cmin
    oveq1
    oveq1d
    oveq12d
    cbvmptv
    oveq1i
    syl6eleq
    taylthlem2
    taylthlem1
end
