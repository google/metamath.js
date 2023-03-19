include "cbs.mm"
include "cfv.mm"
include "c2o.mm"
include "cv.mm"
include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "cixp.mm"
include "crn.mm"
include "cvv.mm"
include "con0.mm"
include "eqid.mm"
include "wcel.mm"
include "csca.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "2on.mm"
include "wfn.mm"
include "xpscfn.mm"
include "syl2anc.mm"
include "prdsbas2.mm"
include "c0.mm"
include "wceq.mm"
include "cif.mm"
include "wa.mm"
include "wi.mm"
include "xpscfv.mm"
include "3expia.mm"
include "imp.mm"
include "fveq2d.mm"
include "ifeq12.mm"
include "mp2an.mm"
include "fvif.mm"
include "eqtr4i.mm"
include "syl6eqr.mm"
include "ixpeq2dva.mm"
include "xpsfrn.mm"
include "eqtr2d.mm"

theorem xpslem
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
  assert |- ( ph -> ran F = ( Base ` U ) )

  proof
    wph
    cU
    cbs
    cfv
    #
    vk
    c2o
    vk
    cv
    #
    cR
    csn
    cS
    csn
    ccda
    co
    ccnv
    #
    cfv
    #
    cbs
    cfv
    #
    cixp
    #
    cF
    crn
    #
    wph
    vk
    @0
    @2
    cG
    c2o
    cvv
    con0
    cU
    xpsval.u
    @0
    eqid
    cG
    cvv
    wcel
    wph
    cG
    cR
    csca
    cfv
    cvv
    xpsval.k
    cR
    csca
    fvex
    eqeltri
    a1i
    c2o
    con0
    wcel
    wph
    2on
    a1i
    wph
    cR
    cV
    wcel
    #
    cS
    cW
    wcel
    #
    @2
    c2o
    wfn
    xpsval.1
    xpsval.2
    cR
    cS
    cV
    cW
    xpscfn
    syl2anc
    prdsbas2
    wph
    @5
    vk
    c2o
    @1
    c0
    wceq
    #
    cX
    cY
    cif
    #
    cixp
    @6
    wph
    vk
    c2o
    @4
    @10
    wph
    @1
    c2o
    wcel
    #
    wa
    #
    @4
    @9
    cR
    cS
    cif
    #
    cbs
    cfv
    #
    @10
    @12
    @3
    @13
    cbs
    wph
    @11
    @3
    @13
    wceq
    #
    wph
    @7
    @8
    @11
    @15
    wi
    xpsval.1
    xpsval.2
    @7
    @8
    @11
    @15
    cR
    cS
    @1
    cV
    cW
    xpscfv
    3expia
    syl2anc
    imp
    fveq2d
    @10
    @9
    cR
    cbs
    cfv
    #
    cS
    cbs
    cfv
    #
    cif
    #
    @14
    cX
    @16
    wceq
    cY
    @17
    wceq
    @10
    @18
    wceq
    xpsval.x
    xpsval.y
    @9
    cX
    @16
    cY
    @17
    ifeq12
    mp2an
    @9
    cR
    cS
    cbs
    fvif
    eqtr4i
    syl6eqr
    ixpeq2dva
    vx
    vy
    cX
    cY
    vk
    cF
    xpsval.f
    xpsfrn
    syl6eqr
    eqtr2d
end
