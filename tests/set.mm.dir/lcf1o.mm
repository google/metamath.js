include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "wrex.mm"
include "crio.mm"
include "cmpt.mm"
include "weq.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "oveq2d.mm"
include "rexbidv.mm"
include "syl5bb.mm"
include "cbvriotav.mm"
include "eqeq1.mm"
include "riotabidv.mm"
include "syl5eq.mm"
include "cbvmptv.mm"
include "sneq.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "rexeqbidv.mm"
include "mpteq2dv.mm"
include "eqtri.mm"
include "lcfrlem9.mm"

theorem lcf1o
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vf: setvar f
  let vk: setvar k
  let cF: class F
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vl: setvar l
  let vu: setvar u
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  assume lcf1o.h: |- H = ( LHyp ` K )
  assume lcf1o.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcf1o.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcf1o.v: |- V = ( Base ` U )
  assume lcf1o.a: |- .+ = ( +g ` U )
  assume lcf1o.t: |- .x. = ( .s ` U )
  assume lcf1o.s: |- S = ( Scalar ` U )
  assume lcf1o.r: |- R = ( Base ` S )
  assume lcf1o.z: |- .0. = ( 0g ` U )
  assume lcf1o.f: |- F = ( LFnl ` U )
  assume lcf1o.l: |- L = ( LKer ` U )
  assume lcf1o.d: |- D = ( LDual ` U )
  assume lcf1o.q: |- Q = ( 0g ` D )
  assume lcf1o.c: |- C = { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }
  assume lcf1o.j: |- J = ( x e. ( V \ { .0. } ) |-> ( v e. V |-> ( iota_ k e. R E. w e. ( ._|_ ` { x } ) v = ( w .+ ( k .x. x ) ) ) ) )
  assume lcflo.k: |- ( ph -> ( K e. HL /\ W e. H ) )

  disjoint f k
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint .+ f
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint .+ k
  disjoint v w
  disjoint v x
  disjoint .+ v
  disjoint w x
  disjoint .+ w
  disjoint .+ x
  disjoint ._|_ f
  disjoint ._|_ k
  disjoint ._|_ v
  disjoint ._|_ w
  disjoint ._|_ x
  disjoint .0. x
  disjoint L f
  disjoint R f
  disjoint R k
  disjoint R v
  disjoint R x
  disjoint F f
  disjoint V f
  disjoint V v
  disjoint V x
  disjoint .x. f
  disjoint .x. k
  disjoint .x. v
  disjoint .x. w
  disjoint .x. x
  disjoint w x
  disjoint ._|_ w
  disjoint ._|_ x
  disjoint .0. x
  disjoint v x
  disjoint V v
  disjoint V x
  disjoint .x. x
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint v w
  disjoint .+ x
  disjoint R x
  disjoint f l
  disjoint f u
  disjoint f y
  disjoint f z
  disjoint k l
  disjoint k u
  disjoint k y
  disjoint k z
  disjoint l u
  disjoint l v
  disjoint l w
  disjoint l x
  disjoint l y
  disjoint l z
  disjoint .+ l
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint .+ u
  disjoint v y
  disjoint v z
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint .+ y
  disjoint .+ z
  disjoint ._|_ l
  disjoint ._|_ u
  disjoint ._|_ y
  disjoint ._|_ z
  disjoint C l
  disjoint C u
  disjoint C y
  disjoint C z
  disjoint .0. l
  disjoint .0. u
  disjoint .0. y
  disjoint .0. z
  disjoint J l
  disjoint J u
  disjoint J y
  disjoint J z
  disjoint L l
  disjoint L u
  disjoint L y
  disjoint L z
  disjoint l ph
  disjoint ph u
  disjoint ph y
  disjoint ph z
  disjoint Q l
  disjoint Q u
  disjoint Q y
  disjoint Q z
  disjoint R l
  disjoint R u
  disjoint R y
  disjoint R z
  disjoint S l
  disjoint S u
  disjoint S y
  disjoint S z
  disjoint U l
  disjoint U y
  disjoint U z
  disjoint V l
  disjoint V u
  disjoint V y
  disjoint V z
  disjoint .x. l
  disjoint .x. u
  disjoint .x. y
  disjoint .x. z
  disjoint X k
  disjoint X v
  disjoint X w
  disjoint X x
  assert |- ( ph -> J : ( V \ { .0. } ) -1-1-onto-> ( C \ { Q } ) )

  proof
    wph
    vy
    vz
    vu
    cC
    cD
    c.pl
    cQ
    cR
    cS
    c.x
    cU
    vf
    vl
    cF
    cH
    cJ
    cK
    cL
    c.pe
    cV
    cW
    c.0
    lcf1o.h
    lcf1o.o
    lcf1o.u
    lcf1o.v
    lcf1o.a
    lcf1o.t
    lcf1o.s
    lcf1o.r
    lcf1o.z
    lcf1o.f
    lcf1o.l
    lcf1o.d
    lcf1o.q
    lcf1o.c
    cJ
    vx
    cV
    c.0
    csn
    cdif
    #
    vv
    cV
    vv
    cv
    #
    vw
    cv
    #
    vk
    cv
    #
    vx
    cv
    #
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vw
    @4
    csn
    #
    c.pe
    cfv
    #
    wrex
    #
    vk
    cR
    crio
    #
    cmpt
    #
    cmpt
    vy
    @0
    vu
    cV
    vu
    cv
    #
    vz
    cv
    #
    vl
    cv
    #
    vy
    cv
    #
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vz
    @16
    csn
    #
    c.pe
    cfv
    #
    wrex
    #
    vl
    cR
    crio
    #
    cmpt
    #
    cmpt
    lcf1o.j
    vx
    vy
    @0
    @12
    @24
    vx
    vy
    weq
    #
    @12
    vu
    cV
    @13
    @14
    @15
    @4
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vz
    @9
    wrex
    #
    vl
    cR
    crio
    #
    cmpt
    @24
    vv
    vu
    cV
    @11
    @30
    vv
    vu
    weq
    #
    @11
    @1
    @27
    wceq
    #
    vz
    @9
    wrex
    #
    vl
    cR
    crio
    @30
    @10
    @33
    vk
    vl
    cR
    @10
    @1
    @14
    @5
    c.pl
    co
    #
    wceq
    #
    vz
    @9
    wrex
    vk
    vl
    weq
    #
    @33
    @7
    @35
    vw
    vz
    @9
    vw
    vz
    weq
    @6
    @34
    @1
    @2
    @14
    @5
    c.pl
    oveq1
    eqeq2d
    cbvrexv
    @36
    @35
    @32
    vz
    @9
    @36
    @34
    @27
    @1
    @36
    @5
    @26
    @14
    c.pl
    @3
    @15
    @4
    c.x
    oveq1
    oveq2d
    eqeq2d
    rexbidv
    syl5bb
    cbvriotav
    @31
    @33
    @29
    vl
    cR
    @31
    @32
    @28
    vz
    @9
    @1
    @13
    @27
    eqeq1
    rexbidv
    riotabidv
    syl5eq
    cbvmptv
    @25
    vu
    cV
    @30
    @23
    @25
    @29
    @22
    vl
    cR
    @25
    @28
    @19
    vz
    @9
    @21
    @25
    @8
    @20
    c.pe
    @4
    @16
    sneq
    fveq2d
    @25
    @27
    @18
    @13
    @25
    @26
    @17
    @14
    c.pl
    @4
    @16
    @15
    c.x
    oveq2
    oveq2d
    eqeq2d
    rexeqbidv
    riotabidv
    mpteq2dv
    syl5eq
    cbvmptv
    eqtri
    lcflo.k
    lcfrlem9
end
