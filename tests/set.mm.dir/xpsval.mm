include "cxps.mm"
include "co.mm"
include "ccnv.mm"
include "cimas.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "elex.mm"
include "syl.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "csn.mm"
include "ccda.mm"
include "cmpt2.mm"
include "csca.mm"
include "cprds.mm"
include "wa.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "mpt2eq12.mm"
include "syl2an.mm"
include "cnveqd.mm"
include "adantr.mm"
include "sneq.mm"
include "oveqan12d.mm"
include "oveq12d.mm"
include "df-xps.mm"
include "ovex.mm"
include "ovmpt2a.mm"
include "syl2anc.mm"
include "syl5eq.mm"

theorem xpsval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vs: setvar s
  let vc: setvar c
  let vk: setvar k
  let cA: class A
  let cB: class B
  let vd: setvar d
  let cC: class C
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let c.x: class .x.
  let c.xp: class .X.
  let c.xb: class .xb
  assume xpsval.t: |- T = ( R Xs. S )
  assume xpsval.x: |- X = ( Base ` R )
  assume xpsval.y: |- Y = ( Base ` S )
  assume xpsval.1: |- ( ph -> R e. V )
  assume xpsval.2: |- ( ph -> S e. W )
  assume xpsval.f: |- F = ( x e. X , y e. Y |-> `' ( { x } +c { y } ) )
  assume xpsval.k: |- G = ( Scalar ` R )
  assume xpsval.u: |- U = ( G Xs_ `' ( { R } +c { S } ) )

  disjoint x y
  disjoint W x
  disjoint X x
  disjoint X y
  disjoint R x
  disjoint Y x
  disjoint Y y
  disjoint r s
  disjoint r y
  disjoint s y
  disjoint c k
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint A x
  disjoint A y
  disjoint B c
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint c d
  disjoint C c
  disjoint d k
  disjoint d x
  disjoint d y
  disjoint C d
  disjoint C k
  disjoint C x
  disjoint C y
  disjoint G k
  disjoint D c
  disjoint D d
  disjoint D k
  disjoint D x
  disjoint D y
  disjoint F r
  disjoint F s
  disjoint c r
  disjoint c s
  disjoint S c
  disjoint d r
  disjoint d s
  disjoint S d
  disjoint k r
  disjoint k s
  disjoint S k
  disjoint S r
  disjoint S s
  disjoint U k
  disjoint U r
  disjoint U s
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a k
  disjoint a ph
  disjoint b c
  disjoint b d
  disjoint b k
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint k ph
  disjoint .x. k
  disjoint .x. x
  disjoint .x. y
  disjoint .X. k
  disjoint .X. x
  disjoint .X. y
  disjoint a x
  disjoint a y
  disjoint X a
  disjoint b x
  disjoint b y
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X k
  disjoint R c
  disjoint R d
  disjoint R k
  disjoint r x
  disjoint R r
  disjoint s x
  disjoint R s
  disjoint .xb a
  disjoint .xb b
  disjoint .xb c
  disjoint .xb d
  disjoint Y a
  disjoint Y b
  disjoint Y c
  disjoint Y d
  disjoint Y k
  assert |- ( ph -> T = ( `' F "s U ) )

  proof
    wph
    cT
    cR
    cS
    cxps
    co
    #
    cF
    ccnv
    #
    cU
    cimas
    co
    #
    xpsval.t
    wph
    cR
    cvv
    wcel
    #
    cS
    cvv
    wcel
    #
    @0
    @2
    wceq
    wph
    cR
    cV
    wcel
    @3
    xpsval.1
    cR
    cV
    elex
    syl
    wph
    cS
    cW
    wcel
    @4
    xpsval.2
    cS
    cW
    elex
    syl
    vr
    vs
    cR
    cS
    cvv
    cvv
    vx
    vy
    vr
    cv
    #
    cbs
    cfv
    #
    vs
    cv
    #
    cbs
    cfv
    #
    vx
    cv
    csn
    vy
    cv
    csn
    ccda
    co
    ccnv
    #
    cmpt2
    #
    ccnv
    #
    @5
    csca
    cfv
    #
    @5
    csn
    #
    @7
    csn
    #
    ccda
    co
    #
    ccnv
    #
    cprds
    co
    #
    cimas
    co
    @2
    cxps
    @5
    cR
    wceq
    #
    @7
    cS
    wceq
    #
    wa
    #
    @11
    @1
    @17
    cU
    cimas
    @20
    @10
    cF
    @20
    @10
    vx
    vy
    cX
    cY
    @9
    cmpt2
    #
    cF
    @18
    @6
    cX
    wceq
    @8
    cY
    wceq
    @10
    @21
    wceq
    @19
    @18
    @6
    cR
    cbs
    cfv
    cX
    @5
    cR
    cbs
    fveq2
    xpsval.x
    syl6eqr
    @19
    @8
    cS
    cbs
    cfv
    cY
    @7
    cS
    cbs
    fveq2
    xpsval.y
    syl6eqr
    vx
    vy
    @6
    @8
    cX
    cY
    @9
    mpt2eq12
    syl2an
    xpsval.f
    syl6eqr
    cnveqd
    @20
    @17
    cG
    cR
    csn
    #
    cS
    csn
    #
    ccda
    co
    #
    ccnv
    #
    cprds
    co
    cU
    @20
    @12
    cG
    @16
    @25
    cprds
    @20
    @12
    cR
    csca
    cfv
    #
    cG
    @18
    @12
    @26
    wceq
    @19
    @5
    cR
    csca
    fveq2
    adantr
    xpsval.k
    syl6eqr
    @20
    @15
    @24
    @18
    @19
    @13
    @22
    @14
    @23
    ccda
    @5
    cR
    sneq
    @7
    cS
    sneq
    oveqan12d
    cnveqd
    oveq12d
    xpsval.u
    syl6eqr
    oveq12d
    vx
    vy
    vs
    vr
    df-xps
    @1
    cU
    cimas
    ovex
    ovmpt2a
    syl2anc
    syl5eq
end
