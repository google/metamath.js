include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cixp.mm"
include "wcel.mm"
include "cop.mm"
include "cco.mm"
include "wceq.mm"
include "chom.mm"
include "wral.mm"
include "wa.mm"
include "eqid.mm"
include "cfunc.mm"
include "wbr.mm"
include "natrcl.mm"
include "syl.mm"
include "simpld.mm"
include "df-br.mm"
include "sylibr.mm"
include "simprd.mm"
include "isnat.mm"
include "mpbid.mm"

theorem natixp
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cL: class L
  let cN: class N
  let vf: setvar f
  let vy: setvar y
  let vz: setvar z
  let cH: class H
  let cR: class R
  let va: setvar a
  let vg: setvar g
  let vh: setvar h
  let vr: setvar r
  let vs: setvar s
  let cX: class X
  let c.x: class .x.
  let cY: class Y
  assume natrcl.1: |- N = ( C Nat D )
  assume natixp.2: |- ( ph -> A e. ( <. F , G >. N <. K , L >. ) )
  assume natixp.b: |- B = ( Base ` C )
  assume natixp.j: |- J = ( Hom ` D )

  disjoint A x
  disjoint F x
  disjoint G x
  disjoint C x
  disjoint K x
  disjoint ph x
  disjoint D x
  disjoint L x
  disjoint B x
  disjoint J x
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F f
  disjoint F y
  disjoint F z
  disjoint G f
  disjoint G y
  disjoint G z
  disjoint H f
  disjoint R f
  disjoint R x
  disjoint R y
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a r
  disjoint a s
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C a
  disjoint f g
  disjoint f h
  disjoint f r
  disjoint f s
  disjoint C f
  disjoint g h
  disjoint g r
  disjoint g s
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint C g
  disjoint h r
  disjoint h s
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint C h
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint C r
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint C s
  disjoint C y
  disjoint C z
  disjoint K f
  disjoint K y
  disjoint K z
  disjoint f ph
  disjoint ph y
  disjoint ph z
  disjoint X f
  disjoint X x
  disjoint X y
  disjoint D a
  disjoint D f
  disjoint D g
  disjoint D h
  disjoint D r
  disjoint D s
  disjoint D y
  disjoint D z
  disjoint L f
  disjoint L y
  disjoint L z
  disjoint .x. f
  disjoint .x. x
  disjoint .x. y
  disjoint Y f
  disjoint Y x
  disjoint Y y
  disjoint B y
  assert |- ( ph -> A e. X_ x e. B ( ( F ` x ) J ( K ` x ) ) )

  proof
    wph
    cA
    vx
    cB
    vx
    cv
    #
    cF
    cfv
    #
    @0
    cK
    cfv
    #
    cJ
    co
    cixp
    wcel
    #
    vy
    cv
    #
    cA
    cfv
    vz
    cv
    #
    @0
    @4
    cG
    co
    cfv
    @1
    @4
    cF
    cfv
    cop
    @4
    cK
    cfv
    #
    cD
    cco
    cfv
    #
    co
    co
    @5
    @0
    @4
    cL
    co
    cfv
    @0
    cA
    cfv
    @1
    @2
    cop
    @6
    @7
    co
    co
    wceq
    vz
    @0
    @4
    cC
    chom
    cfv
    #
    co
    wral
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wph
    cA
    cF
    cG
    cop
    #
    cK
    cL
    cop
    #
    cN
    co
    wcel
    #
    @3
    @9
    wa
    natixp.2
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    @7
    vz
    cF
    cG
    @8
    cJ
    cK
    cL
    cN
    natrcl.1
    natixp.b
    @8
    eqid
    natixp.j
    @7
    eqid
    wph
    @10
    cC
    cD
    cfunc
    co
    #
    wcel
    #
    cF
    cG
    @13
    wbr
    wph
    @14
    @11
    @13
    wcel
    #
    wph
    @12
    @14
    @15
    wa
    natixp.2
    cA
    cC
    cD
    @10
    @11
    cN
    natrcl.1
    natrcl
    syl
    #
    simpld
    cF
    cG
    @13
    df-br
    sylibr
    wph
    @15
    cK
    cL
    @13
    wbr
    wph
    @14
    @15
    @16
    simprd
    cK
    cL
    @13
    df-br
    sylibr
    isnat
    mpbid
    simpld
end
