include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cicc.mm"
include "cz.mm"
include "cin.mm"
include "cdvn.mm"
include "cfv.mm"
include "cfa.mm"
include "cdiv.mm"
include "cmin.mm"
include "cexp.mm"
include "cmul.mm"
include "wb.mm"
include "wceq.mm"
include "0z.mm"
include "nn0zd.mm"
include "fzval2.mm"
include "sylancr.mm"
include "eleq2d.mm"
include "adantr.mm"
include "biimpa.mm"
include "cn0.mm"
include "cpnf.mm"
include "orcd.mm"
include "taylplem1.mm"
include "taylfvallem1.mm"
include "syldan.mm"

theorem taylplem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cN: class N
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cT: class T
  assume taylpfval.s: |- ( ph -> S e. { RR , CC } )
  assume taylpfval.f: |- ( ph -> F : A --> CC )
  assume taylpfval.a: |- ( ph -> A C_ S )
  assume taylpfval.n: |- ( ph -> N e. NN0 )
  assume taylpfval.b: |- ( ph -> B e. dom ( ( S Dn F ) ` N ) )

  disjoint B k
  disjoint F k
  disjoint N k
  disjoint k ph
  disjoint S k
  disjoint X k
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint B u
  disjoint v x
  disjoint v y
  disjoint B v
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F u
  disjoint F v
  disjoint F x
  disjoint F y
  disjoint N u
  disjoint N v
  disjoint N x
  disjoint N y
  disjoint ph u
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint D k
  disjoint D u
  disjoint D v
  disjoint D y
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint X x
  assert |- ( ( ( ph /\ X e. CC ) /\ k e. ( 0 ... N ) ) -> ( ( ( ( ( S Dn F ) ` k ) ` B ) / ( ! ` k ) ) x. ( ( X - B ) ^ k ) ) e. CC )

  proof
    wph
    cX
    cc
    wcel
    #
    wa
    #
    vk
    cv
    #
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    @2
    cc0
    cN
    cicc
    co
    cz
    cin
    #
    wcel
    #
    cB
    @2
    cS
    cF
    cdvn
    co
    cfv
    cfv
    @2
    cfa
    cfv
    cdiv
    co
    cX
    cB
    cmin
    co
    @2
    cexp
    co
    cmul
    co
    cc
    wcel
    @1
    @4
    @6
    wph
    @4
    @6
    wb
    @0
    wph
    @3
    @5
    @2
    wph
    cc0
    cz
    wcel
    cN
    cz
    wcel
    @3
    @5
    wceq
    0z
    wph
    cN
    taylpfval.n
    nn0zd
    cc0
    cN
    fzval2
    sylancr
    eleq2d
    adantr
    biimpa
    wph
    cA
    cB
    cS
    vk
    cF
    cN
    cX
    taylpfval.s
    taylpfval.f
    taylpfval.a
    wph
    cN
    cn0
    wcel
    cN
    cpnf
    wceq
    taylpfval.n
    orcd
    wph
    cA
    cB
    cS
    vk
    cF
    cN
    taylpfval.s
    taylpfval.f
    taylpfval.a
    taylpfval.n
    taylpfval.b
    taylplem1
    taylfvallem1
    syldan
end
