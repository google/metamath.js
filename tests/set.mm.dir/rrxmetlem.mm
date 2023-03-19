include "cc0.mm"
include "csupp.mm"
include "co.mm"
include "cun.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "sstrd.mm"
include "sselda.mm"
include "cr.mm"
include "rrxf.mm"
include "ffvelrnda.mm"
include "recnd.mm"
include "syldan.mm"
include "subcld.mm"
include "sqcld.mm"
include "cdif.mm"
include "wceq.mm"
include "ssdifd.mm"
include "simpr.mm"
include "eldifad.mm"
include "wss.mm"
include "ssun1.mm"
include "a1i.mm"
include "0red.mm"
include "suppssr.mm"
include "ssun2.mm"
include "eqtr4d.mm"
include "subeq0bd.mm"
include "sq0id.mm"
include "fsumss.mm"

theorem rrxmetlem
  let wph: wff ph
  let cA: class A
  let cD: class D
  let vh: setvar h
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume rrxmval.1: |- X = { h e. ( RR ^m I ) | h finSupp 0 }
  assume rrxmval.d: |- D = ( dist ` ( RR^ ` I ) )
  assume rrxmetlem.1: |- ( ph -> I e. V )
  assume rrxmetlem.2: |- ( ph -> F e. X )
  assume rrxmetlem.3: |- ( ph -> G e. X )
  assume rrxmetlem.4: |- ( ph -> A C_ I )
  assume rrxmetlem.5: |- ( ph -> A e. Fin )
  assume rrxmetlem.6: |- ( ph -> ( ( F supp 0 ) u. ( G supp 0 ) ) C_ A )

  disjoint k ph
  disjoint A k
  disjoint F h
  disjoint F k
  disjoint h k
  disjoint G h
  disjoint G k
  disjoint I h
  disjoint I k
  disjoint V h
  disjoint V k
  disjoint X k
  disjoint D f
  disjoint D g
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint f h
  disjoint f k
  disjoint g h
  disjoint g k
  disjoint h x
  disjoint k x
  disjoint G f
  disjoint G g
  disjoint G x
  disjoint I f
  disjoint I g
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint h y
  disjoint h z
  disjoint k y
  disjoint k z
  disjoint V f
  disjoint V g
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint X f
  disjoint X g
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> sum_ k e. ( ( F supp 0 ) u. ( G supp 0 ) ) ( ( ( F ` k ) - ( G ` k ) ) ^ 2 ) = sum_ k e. A ( ( ( F ` k ) - ( G ` k ) ) ^ 2 ) )

  proof
    wph
    cF
    cc0
    csupp
    co
    #
    cG
    cc0
    csupp
    co
    #
    cun
    #
    cA
    vk
    cv
    #
    cF
    cfv
    #
    @3
    cG
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vk
    rrxmetlem.6
    wph
    @3
    @2
    wcel
    #
    wa
    #
    @6
    @9
    @4
    @5
    wph
    @8
    @3
    cI
    wcel
    #
    @4
    cc
    wcel
    #
    wph
    @2
    cI
    @3
    wph
    @2
    cA
    cI
    rrxmetlem.6
    rrxmetlem.4
    sstrd
    sselda
    #
    wph
    @10
    wa
    #
    @4
    wph
    cI
    cr
    @3
    cF
    wph
    vh
    cF
    cI
    cX
    rrxmval.1
    rrxmetlem.2
    rrxf
    #
    ffvelrnda
    recnd
    #
    syldan
    wph
    @8
    @10
    @5
    cc
    wcel
    @12
    @13
    @5
    wph
    cI
    cr
    @3
    cG
    wph
    vh
    cG
    cI
    cX
    rrxmval.1
    rrxmetlem.3
    rrxf
    #
    ffvelrnda
    recnd
    syldan
    subcld
    sqcld
    wph
    @3
    cA
    @2
    cdif
    #
    wcel
    @3
    cI
    @2
    cdif
    #
    wcel
    #
    @7
    cc0
    wceq
    wph
    @17
    @18
    @3
    wph
    cA
    cI
    @2
    rrxmetlem.4
    ssdifd
    sselda
    wph
    @19
    wa
    #
    @6
    @20
    @4
    @5
    wph
    @19
    @10
    @11
    @20
    @3
    cI
    @2
    wph
    @19
    simpr
    eldifad
    @15
    syldan
    @20
    @4
    cc0
    @5
    wph
    cI
    cr
    cr
    cF
    cV
    @2
    @3
    cc0
    @14
    @0
    @2
    wss
    wph
    @0
    @1
    ssun1
    a1i
    rrxmetlem.1
    wph
    0red
    #
    suppssr
    wph
    cI
    cr
    cr
    cG
    cV
    @2
    @3
    cc0
    @16
    @1
    @2
    wss
    wph
    @1
    @0
    ssun2
    a1i
    rrxmetlem.1
    @21
    suppssr
    eqtr4d
    subeq0bd
    sq0id
    syldan
    rrxmetlem.5
    fsumss
end
