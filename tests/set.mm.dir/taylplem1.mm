include "cv.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "cz.mm"
include "cin.mm"
include "wcel.mm"
include "cfz.mm"
include "cdvn.mm"
include "cfv.mm"
include "cdm.mm"
include "wceq.mm"
include "0z.mm"
include "nn0zd.mm"
include "fzval2.mm"
include "sylancr.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "wa.mm"
include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "cpm.mm"
include "wss.mm"
include "cvv.mm"
include "wf.mm"
include "cnex.mm"
include "a1i.mm"
include "elpm2r.mm"
include "syl22anc.mm"
include "jca.mm"
include "dvn2bss.mm"
include "3expa.mm"
include "sylan.mm"
include "adantr.mm"
include "sseldd.mm"
include "syldan.mm"

theorem taylplem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cN: class N
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cT: class T
  let cX: class X
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
  disjoint X k
  disjoint X x
  assert |- ( ( ph /\ k e. ( ( 0 [,] N ) i^i ZZ ) ) -> B e. dom ( ( S Dn F ) ` k ) )

  proof
    wph
    vk
    cv
    #
    cc0
    cN
    cicc
    co
    cz
    cin
    #
    wcel
    #
    @0
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    cB
    @0
    cS
    cF
    cdvn
    co
    #
    cfv
    cdm
    #
    wcel
    wph
    @4
    @2
    wph
    @3
    @1
    @0
    wph
    cc0
    cz
    wcel
    cN
    cz
    wcel
    @3
    @1
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
    biimpar
    wph
    @4
    wa
    cN
    @5
    cfv
    cdm
    #
    @6
    cB
    wph
    cS
    cr
    cc
    cpr
    #
    wcel
    #
    cF
    cc
    cS
    cpm
    co
    wcel
    #
    wa
    @4
    @7
    @6
    wss
    #
    wph
    @9
    @10
    taylpfval.s
    wph
    cc
    cvv
    wcel
    #
    @9
    cA
    cc
    cF
    wf
    cA
    cS
    wss
    @10
    @12
    wph
    cnex
    a1i
    taylpfval.s
    taylpfval.f
    taylpfval.a
    cc
    cS
    cA
    cF
    cvv
    @8
    elpm2r
    syl22anc
    jca
    @9
    @10
    @4
    @11
    cS
    cF
    @0
    cN
    dvn2bss
    3expa
    sylan
    wph
    cB
    @7
    wcel
    @4
    taylpfval.b
    adantr
    sseldd
    syldan
end
