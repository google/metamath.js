include "ccrg.mm"
include "wcel.mm"
include "crg.mm"
include "crngring.mm"
include "syl.mm"
include "cv.mm"
include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "mplcrng.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eqid.mm"
include "simprr.mm"
include "mvrcl.mm"
include "simprl.mm"
include "cmulr.mm"
include "mgpplusg.mm"
include "eqcomi.mm"
include "crngcom.mm"
include "syl3anc.mm"
include "ralrimivva.mm"
include "mplcoe5.mm"

theorem mplcoe2
  let wph: wff ph
  let vy: setvar y
  let cD: class D
  let cP: class P
  let cR: class R
  let c.1: class .1.
  let vf: setvar f
  let vk: setvar k
  let c.ex: class .^
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  let vi: setvar i
  let vn: setvar n
  let vw: setvar w
  let vx: setvar x
  let vz: setvar z
  let cB: class B
  let cN: class N
  let cX: class X
  let c.x: class .x.
  assume mplcoe1.p: |- P = ( I mPoly R )
  assume mplcoe1.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume mplcoe1.z: |- .0. = ( 0g ` R )
  assume mplcoe1.o: |- .1. = ( 1r ` R )
  assume mplcoe1.i: |- ( ph -> I e. W )
  assume mplcoe2.g: |- G = ( mulGrp ` P )
  assume mplcoe2.m: |- .^ = ( .g ` G )
  assume mplcoe2.v: |- V = ( I mVar R )
  assume mplcoe2.r: |- ( ph -> R e. CRing )
  assume mplcoe2.y: |- ( ph -> Y e. D )

  disjoint .^ k
  disjoint k y
  disjoint .1. k
  disjoint .1. y
  disjoint G k
  disjoint f k
  disjoint f y
  disjoint I f
  disjoint I k
  disjoint I y
  disjoint k ph
  disjoint ph y
  disjoint R f
  disjoint R y
  disjoint D k
  disjoint D y
  disjoint P k
  disjoint V k
  disjoint .0. f
  disjoint .0. k
  disjoint .0. y
  disjoint Y f
  disjoint Y k
  disjoint Y y
  disjoint W k
  disjoint W y
  disjoint G y
  disjoint V y
  disjoint .^ y
  disjoint i k
  disjoint i n
  disjoint i w
  disjoint i x
  disjoint i z
  disjoint .^ i
  disjoint k n
  disjoint k w
  disjoint k x
  disjoint k z
  disjoint n w
  disjoint n x
  disjoint n z
  disjoint .^ n
  disjoint w x
  disjoint w z
  disjoint .^ w
  disjoint x z
  disjoint .^ x
  disjoint .^ z
  disjoint i y
  disjoint .1. i
  disjoint n y
  disjoint .1. n
  disjoint w y
  disjoint .1. w
  disjoint x y
  disjoint .1. x
  disjoint y z
  disjoint .1. z
  disjoint B k
  disjoint G i
  disjoint G w
  disjoint G x
  disjoint G z
  disjoint f i
  disjoint f n
  disjoint f w
  disjoint f x
  disjoint f z
  disjoint I i
  disjoint I n
  disjoint I w
  disjoint I x
  disjoint I z
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint i ph
  disjoint n ph
  disjoint ph w
  disjoint ph x
  disjoint ph z
  disjoint D i
  disjoint D n
  disjoint D w
  disjoint D x
  disjoint D z
  disjoint P i
  disjoint P w
  disjoint P x
  disjoint P z
  disjoint V i
  disjoint V n
  disjoint V w
  disjoint V x
  disjoint V z
  disjoint .0. i
  disjoint .0. n
  disjoint .0. w
  disjoint .0. x
  disjoint .0. z
  disjoint X f
  disjoint X k
  disjoint X n
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y i
  disjoint Y w
  disjoint Y x
  disjoint Y z
  disjoint W i
  disjoint .x. k
  disjoint .x. w
  disjoint .x. x
  disjoint .x. z
  assert |- ( ph -> ( y e. D |-> if ( y = Y , .1. , .0. ) ) = ( G gsum ( k e. I |-> ( ( Y ` k ) .^ ( V ` k ) ) ) ) )

  proof
    wph
    vx
    vy
    cD
    cP
    cR
    c.1
    vf
    vk
    c.ex
    cG
    cI
    cV
    cW
    cY
    c.0
    mplcoe1.p
    mplcoe1.d
    mplcoe1.z
    mplcoe1.o
    mplcoe1.i
    mplcoe2.g
    mplcoe2.m
    mplcoe2.v
    wph
    cR
    ccrg
    wcel
    #
    cR
    crg
    wcel
    #
    mplcoe2.r
    cR
    crngring
    syl
    #
    mplcoe2.y
    wph
    vy
    cv
    #
    cV
    cfv
    #
    vx
    cv
    #
    cV
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    @6
    @4
    @7
    co
    wceq
    #
    vx
    vy
    cI
    cI
    wph
    @5
    cI
    wcel
    #
    @3
    cI
    wcel
    #
    wa
    #
    wa
    #
    cP
    ccrg
    wcel
    #
    @4
    cP
    cbs
    cfv
    #
    wcel
    @6
    @14
    wcel
    @8
    wph
    @13
    @11
    wph
    cI
    cW
    wcel
    #
    @0
    @13
    mplcoe1.i
    mplcoe2.r
    cP
    cR
    cI
    cW
    mplcoe1.p
    mplcrng
    syl2anc
    adantr
    @12
    @14
    cP
    cR
    cI
    cV
    cW
    @3
    mplcoe1.p
    mplcoe2.v
    @14
    eqid
    #
    wph
    @15
    @11
    mplcoe1.i
    adantr
    #
    wph
    @1
    @11
    @2
    adantr
    #
    wph
    @9
    @10
    simprr
    mvrcl
    @12
    @14
    cP
    cR
    cI
    cV
    cW
    @5
    mplcoe1.p
    mplcoe2.v
    @16
    @17
    @18
    wph
    @9
    @10
    simprl
    mvrcl
    @14
    cP
    @7
    @4
    @6
    @16
    cP
    cmulr
    cfv
    #
    @7
    cP
    @19
    cG
    mplcoe2.g
    @19
    eqid
    mgpplusg
    eqcomi
    crngcom
    syl3anc
    ralrimivva
    mplcoe5
end
