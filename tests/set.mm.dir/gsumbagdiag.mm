include "cv.mm"
include "cmin.mm"
include "cof.mm"
include "co.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "crab.mm"
include "cxp.mm"
include "cfn.mm"
include "cvv.mm"
include "c0g.mm"
include "cfv.mm"
include "eqid.mm"
include "wcel.mm"
include "psrbaglefi.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "wa.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cn0.mm"
include "cmap.mm"
include "ovex.mm"
include "rab2ex.mm"
include "a1i.mm"
include "xpfi.mm"
include "wn.mm"
include "wceq.mm"
include "simprl.mm"
include "gsumbagdiaglem.mm"
include "simpld.mm"
include "brxp.mm"
include "sylanbrc.mm"
include "pm2.24d.mm"
include "impr.mm"
include "impbida.mm"
include "gsumcom2.mm"

theorem gsumbagdiag
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cD: class D
  let cS: class S
  let vf: setvar f
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cY: class Y
  assume psrbag.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume psrbagconf1o.1: |- S = { y e. D | y oR <_ F }
  assume gsumbagdiag.i: |- ( ph -> I e. V )
  assume gsumbagdiag.f: |- ( ph -> F e. D )
  assume gsumbagdiag.b: |- B = ( Base ` G )
  assume gsumbagdiag.g: |- ( ph -> G e. CMnd )
  assume gsumbagdiag.x: |- ( ( ph /\ ( j e. S /\ k e. { x e. D | x oR <_ ( F oF - j ) } ) ) -> X e. B )

  disjoint f j
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint j k
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint k x
  disjoint k y
  disjoint F k
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G f
  disjoint G j
  disjoint G k
  disjoint G x
  disjoint G y
  disjoint V x
  disjoint V y
  disjoint I f
  disjoint I x
  disjoint I y
  disjoint j ph
  disjoint k ph
  disjoint S j
  disjoint S k
  disjoint S x
  disjoint B j
  disjoint B k
  disjoint D j
  disjoint D k
  disjoint D x
  disjoint D y
  disjoint X f
  disjoint X x
  disjoint X y
  disjoint f m
  disjoint f n
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f z
  disjoint j m
  disjoint j n
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j z
  disjoint k m
  disjoint k n
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k z
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint G m
  disjoint G n
  disjoint V m
  disjoint V n
  disjoint V z
  disjoint I m
  disjoint I n
  disjoint I w
  disjoint I z
  disjoint m ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph z
  disjoint S m
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S z
  disjoint B m
  disjoint D m
  disjoint D n
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D z
  disjoint X m
  disjoint X n
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint Y f
  disjoint Y k
  disjoint Y m
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  assert |- ( ph -> ( G gsum ( j e. S , k e. { x e. D | x oR <_ ( F oF - j ) } |-> X ) ) = ( G gsum ( k e. S , j e. { x e. D | x oR <_ ( F oF - k ) } |-> X ) ) )

  proof
    wph
    cS
    cB
    vx
    cv
    #
    cF
    vj
    cv
    #
    cmin
    cof
    #
    co
    cle
    cofr
    #
    wbr
    #
    vx
    cD
    crab
    #
    cS
    cS
    cS
    cxp
    #
    vj
    vk
    @0
    cF
    vk
    cv
    #
    @2
    co
    @3
    wbr
    vx
    cD
    crab
    #
    cG
    cfn
    cvv
    cX
    cfn
    cG
    c0g
    cfv
    #
    gsumbagdiag.b
    @9
    eqid
    gsumbagdiag.g
    wph
    cS
    vy
    cv
    cF
    @3
    wbr
    vy
    cD
    crab
    #
    cfn
    psrbagconf1o.1
    wph
    cI
    cV
    wcel
    cF
    cD
    wcel
    @10
    cfn
    wcel
    gsumbagdiag.i
    gsumbagdiag.f
    vy
    cD
    vf
    cF
    cI
    cV
    psrbag.d
    psrbaglefi
    syl2anc
    syl5eqel
    #
    @5
    cvv
    wcel
    wph
    @1
    cS
    wcel
    #
    wa
    @4
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vx
    vf
    cn0
    cI
    cmap
    co
    cD
    psrbag.d
    cn0
    cI
    cmap
    ovex
    rab2ex
    a1i
    gsumbagdiag.x
    wph
    cS
    cfn
    wcel
    #
    @13
    @6
    cfn
    wcel
    @11
    @11
    cS
    cS
    xpfi
    syl2anc
    wph
    @12
    @7
    @5
    wcel
    #
    wa
    #
    @1
    @7
    @6
    wbr
    #
    wn
    cX
    @9
    wceq
    #
    wph
    @15
    wa
    #
    @16
    @17
    @18
    @12
    @7
    cS
    wcel
    #
    @16
    wph
    @12
    @14
    simprl
    @18
    @19
    @1
    @8
    wcel
    #
    wph
    vx
    vy
    cD
    cS
    vf
    cF
    cI
    cV
    @1
    @7
    psrbag.d
    psrbagconf1o.1
    gsumbagdiag.i
    gsumbagdiag.f
    gsumbagdiaglem
    #
    simpld
    @1
    @7
    cS
    cS
    brxp
    sylanbrc
    pm2.24d
    impr
    @11
    wph
    @15
    @19
    @20
    wa
    @21
    wph
    vx
    vy
    cD
    cS
    vf
    cF
    cI
    cV
    @7
    @1
    psrbag.d
    psrbagconf1o.1
    gsumbagdiag.i
    gsumbagdiag.f
    gsumbagdiaglem
    impbida
    gsumcom2
end
