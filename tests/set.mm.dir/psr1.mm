include "cv.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt.mm"
include "cbs.mm"
include "cfv.mm"
include "wcel.mm"
include "cmulr.mm"
include "co.mm"
include "wa.mm"
include "wral.mm"
include "eqid.mm"
include "psr1cl.mm"
include "adantr.mm"
include "crg.mm"
include "simpr.mm"
include "psrlidm.mm"
include "psrridm.mm"
include "jca.mm"
include "ralrimiva.mm"
include "wb.mm"
include "psrring.mm"
include "isringid.mm"
include "syl.mm"
include "mpbi2and.mm"

theorem psr1
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cR: class R
  let cS: class S
  let cU: class U
  let c.1: class .1.
  let vf: setvar f
  let cI: class I
  let cV: class V
  let c.0: class .0.
  let vk: setvar k
  let c.pl: class .+
  let vy: setvar y
  let vz: setvar z
  let vg: setvar g
  let vh: setvar h
  let vj: setvar j
  let vn: setvar n
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let cK: class K
  let vu: setvar u
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cX: class X
  let c.x: class .x.
  let cZ: class Z
  let c.xp: class .X.
  let cY: class Y
  assume psrring.s: |- S = ( I mPwSer R )
  assume psrring.i: |- ( ph -> I e. V )
  assume psrring.r: |- ( ph -> R e. Ring )
  assume psr1.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume psr1.z: |- .0. = ( 0g ` R )
  assume psr1.o: |- .1. = ( 1r ` R )
  assume psr1.u: |- U = ( 1r ` S )

  disjoint f x
  disjoint .0. f
  disjoint .0. x
  disjoint I f
  disjoint I x
  disjoint R f
  disjoint R x
  disjoint D x
  disjoint ph x
  disjoint V x
  disjoint S x
  disjoint .1. x
  disjoint k x
  disjoint .+ k
  disjoint .+ x
  disjoint f y
  disjoint f z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint .0. y
  disjoint .0. z
  disjoint f g
  disjoint f h
  disjoint f j
  disjoint f k
  disjoint f n
  disjoint f r
  disjoint f s
  disjoint f t
  disjoint f w
  disjoint g h
  disjoint g j
  disjoint g k
  disjoint g n
  disjoint g r
  disjoint g s
  disjoint g t
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint I g
  disjoint h j
  disjoint h k
  disjoint h n
  disjoint h r
  disjoint h s
  disjoint h t
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint I h
  disjoint j k
  disjoint j n
  disjoint j r
  disjoint j s
  disjoint j t
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint I j
  disjoint k n
  disjoint k r
  disjoint k s
  disjoint k t
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint I k
  disjoint n r
  disjoint n s
  disjoint n t
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint I n
  disjoint r s
  disjoint r t
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint I r
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint I s
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint I t
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint I w
  disjoint I y
  disjoint I z
  disjoint K k
  disjoint k u
  disjoint k v
  disjoint A k
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint B j
  disjoint B k
  disjoint B n
  disjoint B x
  disjoint B z
  disjoint f u
  disjoint f v
  disjoint g u
  disjoint g v
  disjoint R g
  disjoint h u
  disjoint h v
  disjoint R h
  disjoint j u
  disjoint j v
  disjoint R j
  disjoint R k
  disjoint n u
  disjoint n v
  disjoint R n
  disjoint r u
  disjoint r v
  disjoint R r
  disjoint s u
  disjoint s v
  disjoint R s
  disjoint t u
  disjoint t v
  disjoint R t
  disjoint u y
  disjoint u z
  disjoint R u
  disjoint v y
  disjoint v z
  disjoint R v
  disjoint R w
  disjoint R y
  disjoint R z
  disjoint D g
  disjoint D h
  disjoint D j
  disjoint D k
  disjoint D n
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D y
  disjoint D z
  disjoint U y
  disjoint U z
  disjoint X f
  disjoint X g
  disjoint X h
  disjoint X j
  disjoint X k
  disjoint X n
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint ph r
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint V g
  disjoint V h
  disjoint V j
  disjoint V k
  disjoint V r
  disjoint V w
  disjoint V y
  disjoint .x. k
  disjoint .x. x
  disjoint .x. y
  disjoint Z f
  disjoint Z g
  disjoint Z h
  disjoint Z j
  disjoint Z k
  disjoint Z n
  disjoint Z x
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S y
  disjoint S z
  disjoint .1. y
  disjoint .X. j
  disjoint .X. k
  disjoint .X. x
  disjoint Y f
  disjoint Y g
  disjoint Y h
  disjoint Y j
  disjoint Y k
  disjoint Y n
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  assert |- ( ph -> U = ( x e. D |-> if ( x = ( I X. { 0 } ) , .1. , .0. ) ) )

  proof
    wph
    vx
    cD
    vx
    cv
    cI
    cc0
    csn
    cxp
    wceq
    c.1
    c.0
    cif
    cmpt
    #
    cS
    cbs
    cfv
    #
    wcel
    #
    @0
    vy
    cv
    #
    cS
    cmulr
    cfv
    #
    co
    @3
    wceq
    #
    @3
    @0
    @4
    co
    @3
    wceq
    #
    wa
    #
    vy
    @1
    wral
    #
    cU
    @0
    wceq
    #
    wph
    vx
    @1
    cD
    cR
    cS
    @0
    c.1
    vf
    cI
    cV
    c.0
    psrring.s
    psrring.i
    psrring.r
    psr1.d
    psr1.z
    psr1.o
    @0
    eqid
    #
    @1
    eqid
    #
    psr1cl
    wph
    @7
    vy
    @1
    wph
    @3
    @1
    wcel
    #
    wa
    #
    @5
    @6
    @13
    vx
    @1
    cD
    cR
    cS
    @4
    @0
    c.1
    vf
    cI
    cV
    @3
    c.0
    psrring.s
    wph
    cI
    cV
    wcel
    @12
    psrring.i
    adantr
    #
    wph
    cR
    crg
    wcel
    @12
    psrring.r
    adantr
    #
    psr1.d
    psr1.z
    psr1.o
    @10
    @11
    @4
    eqid
    #
    wph
    @12
    simpr
    #
    psrlidm
    @13
    vx
    @1
    cD
    cR
    cS
    @4
    @0
    c.1
    vf
    cI
    cV
    @3
    c.0
    psrring.s
    @14
    @15
    psr1.d
    psr1.z
    psr1.o
    @10
    @11
    @16
    @17
    psrridm
    jca
    ralrimiva
    wph
    cS
    crg
    wcel
    @2
    @8
    wa
    @9
    wb
    wph
    cR
    cS
    cI
    cV
    psrring.s
    psrring.i
    psrring.r
    psrring
    vy
    @1
    cS
    @4
    cU
    @0
    @11
    @16
    psr1.u
    isringid
    syl
    mpbi2and
end
