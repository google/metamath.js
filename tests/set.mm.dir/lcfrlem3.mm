include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "lcfrlem1.mm"
include "clvec.mm"
include "co.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "cbs.mm"
include "eqid.mm"
include "crg.mm"
include "lmodring.mm"
include "cdr.mm"
include "wne.mm"
include "lvecdrng.mm"
include "lflcl.mm"
include "syl3anc.mm"
include "drnginvrcl.mm"
include "ringcl.mm"
include "ldualvscl.mm"
include "ldualvsubcl.mm"
include "syl5eqel.mm"
include "ellkr2.mm"
include "mpbird.mm"

theorem lcfrlem3
  let wph: wff ph
  let cD: class D
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let cV: class V
  let cX: class X
  let c.0: class .0.
  assume lcfrlem1.v: |- V = ( Base ` U )
  assume lcfrlem1.s: |- S = ( Scalar ` U )
  assume lcfrlem1.q: |- .X. = ( .r ` S )
  assume lcfrlem1.z: |- .0. = ( 0g ` S )
  assume lcfrlem1.i: |- I = ( invr ` S )
  assume lcfrlem1.f: |- F = ( LFnl ` U )
  assume lcfrlem1.d: |- D = ( LDual ` U )
  assume lcfrlem1.t: |- .x. = ( .s ` D )
  assume lcfrlem1.m: |- .- = ( -g ` D )
  assume lcfrlem1.u: |- ( ph -> U e. LVec )
  assume lcfrlem1.e: |- ( ph -> E e. F )
  assume lcfrlem1.g: |- ( ph -> G e. F )
  assume lcfrlem1.x: |- ( ph -> X e. V )
  assume lcfrlem1.n: |- ( ph -> ( G ` X ) =/= .0. )
  assume lcfrlem1.h: |- H = ( E .- ( ( ( I ` ( G ` X ) ) .X. ( E ` X ) ) .x. G ) )
  assume lcfrlem2.l: |- L = ( LKer ` U )


  assert |- ( ph -> X e. ( L ` H ) )

  proof
    wph
    cX
    cH
    cL
    cfv
    wcel
    cX
    cH
    cfv
    c.0
    wceq
    wph
    cD
    cS
    c.x
    c.xp
    cU
    cE
    cF
    cG
    cH
    cI
    c.mi
    cV
    cX
    c.0
    lcfrlem1.v
    lcfrlem1.s
    lcfrlem1.q
    lcfrlem1.z
    lcfrlem1.i
    lcfrlem1.f
    lcfrlem1.d
    lcfrlem1.t
    lcfrlem1.m
    lcfrlem1.u
    lcfrlem1.e
    lcfrlem1.g
    lcfrlem1.x
    lcfrlem1.n
    lcfrlem1.h
    lcfrlem1
    wph
    cS
    cF
    cH
    cL
    cV
    cU
    cX
    clvec
    c.0
    lcfrlem1.v
    lcfrlem1.s
    lcfrlem1.z
    lcfrlem1.f
    lcfrlem2.l
    lcfrlem1.u
    wph
    cH
    cE
    cX
    cG
    cfv
    #
    cI
    cfv
    #
    cX
    cE
    cfv
    #
    c.xp
    co
    #
    cG
    c.x
    co
    #
    c.mi
    co
    cF
    lcfrlem1.h
    wph
    cD
    cF
    cE
    @4
    c.mi
    cU
    lcfrlem1.f
    lcfrlem1.d
    lcfrlem1.m
    wph
    cU
    clvec
    wcel
    #
    cU
    clmod
    wcel
    #
    lcfrlem1.u
    cU
    lveclmod
    syl
    #
    lcfrlem1.e
    wph
    cD
    cS
    c.x
    cF
    cG
    cS
    cbs
    cfv
    #
    cU
    @3
    lcfrlem1.f
    lcfrlem1.s
    @8
    eqid
    #
    lcfrlem1.d
    lcfrlem1.t
    @7
    wph
    cS
    crg
    wcel
    #
    @1
    @8
    wcel
    #
    @2
    @8
    wcel
    #
    @3
    @8
    wcel
    wph
    @6
    @10
    @7
    cS
    cU
    lcfrlem1.s
    lmodring
    syl
    wph
    cS
    cdr
    wcel
    #
    @0
    @8
    wcel
    #
    @0
    c.0
    wne
    @11
    wph
    @5
    @13
    lcfrlem1.u
    cS
    cU
    lcfrlem1.s
    lvecdrng
    syl
    wph
    @5
    cG
    cF
    wcel
    cX
    cV
    wcel
    #
    @14
    lcfrlem1.u
    lcfrlem1.g
    lcfrlem1.x
    cS
    cF
    cG
    @8
    cV
    cU
    cX
    clvec
    lcfrlem1.s
    @9
    lcfrlem1.v
    lcfrlem1.f
    lflcl
    syl3anc
    lcfrlem1.n
    @8
    cS
    cI
    @0
    c.0
    @9
    lcfrlem1.z
    lcfrlem1.i
    drnginvrcl
    syl3anc
    wph
    @5
    cE
    cF
    wcel
    @15
    @12
    lcfrlem1.u
    lcfrlem1.e
    lcfrlem1.x
    cS
    cF
    cE
    @8
    cV
    cU
    cX
    clvec
    lcfrlem1.s
    @9
    lcfrlem1.v
    lcfrlem1.f
    lflcl
    syl3anc
    @8
    cS
    c.xp
    @1
    @2
    @9
    lcfrlem1.q
    ringcl
    syl3anc
    lcfrlem1.g
    ldualvscl
    ldualvsubcl
    syl5eqel
    lcfrlem1.x
    ellkr2
    mpbird
end
