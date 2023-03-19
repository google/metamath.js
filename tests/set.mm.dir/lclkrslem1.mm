include "co.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "wcel.mm"
include "wss.mm"
include "eqid.mm"
include "lcfls1c.mm"
include "simplbi.mm"
include "syl.mm"
include "lclkrlem1.mm"
include "chlt.mm"
include "wa.mm"
include "cbs.mm"
include "dvhlmod.mm"
include "w3a.mm"
include "lcfls1lem.mm"
include "sylib.mm"
include "simp1d.mm"
include "ldualvscl.mm"
include "lkrssv.mm"
include "dvhlvec.mm"
include "lkrss.mm"
include "dochss.mm"
include "syl3anc.mm"
include "simp3d.mm"
include "sstrd.mm"
include "sylanbrc.mm"

theorem lclkrslem1
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  assume lclkrslem1.h: |- H = ( LHyp ` K )
  assume lclkrslem1.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lclkrslem1.u: |- U = ( ( DVecH ` K ) ` W )
  assume lclkrslem1.s: |- S = ( LSubSp ` U )
  assume lclkrslem1.f: |- F = ( LFnl ` U )
  assume lclkrslem1.l: |- L = ( LKer ` U )
  assume lclkrslem1.d: |- D = ( LDual ` U )
  assume lclkrslem1.r: |- R = ( Scalar ` U )
  assume lclkrslem1.b: |- B = ( Base ` R )
  assume lclkrslem1.t: |- .x. = ( .s ` D )
  assume lclkrslem1.c: |- C = { f e. F | ( ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) /\ ( ._|_ ` ( L ` f ) ) C_ Q ) }
  assume lclkrslem1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lclkrslem1.q: |- ( ph -> Q e. S )
  assume lclkrslem1.g: |- ( ph -> G e. C )
  assume lclkrslem1.x: |- ( ph -> X e. B )

  disjoint ._|_ f
  disjoint F f
  disjoint G f
  disjoint L f
  disjoint Q f
  disjoint .x. f
  disjoint X f
  assert |- ( ph -> ( X .x. G ) e. C )

  proof
    wph
    cX
    cG
    c.x
    co
    #
    vf
    cv
    cL
    cfv
    #
    c.pe
    cfv
    c.pe
    cfv
    @1
    wceq
    vf
    cF
    crab
    #
    wcel
    @0
    cL
    cfv
    #
    c.pe
    cfv
    #
    cQ
    wss
    @0
    cC
    wcel
    wph
    cB
    @2
    cD
    cR
    c.x
    cU
    vf
    cF
    cG
    cH
    cK
    cL
    c.pe
    cW
    cX
    lclkrslem1.h
    lclkrslem1.o
    lclkrslem1.u
    lclkrslem1.f
    lclkrslem1.l
    lclkrslem1.d
    lclkrslem1.r
    lclkrslem1.b
    lclkrslem1.t
    @2
    eqid
    #
    lclkrslem1.k
    lclkrslem1.x
    wph
    cG
    cC
    wcel
    #
    cG
    @2
    wcel
    #
    lclkrslem1.g
    @6
    @7
    cG
    cL
    cfv
    #
    c.pe
    cfv
    #
    cQ
    wss
    #
    cC
    @2
    cQ
    vf
    cF
    cG
    cL
    c.pe
    lclkrslem1.c
    @5
    lcfls1c
    simplbi
    syl
    lclkrlem1
    wph
    @4
    @9
    cQ
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @3
    cU
    cbs
    cfv
    #
    wss
    @8
    @3
    wss
    @4
    @9
    wss
    lclkrslem1.k
    wph
    cF
    @0
    cL
    @11
    cU
    @11
    eqid
    #
    lclkrslem1.f
    lclkrslem1.l
    wph
    cU
    cH
    cK
    cW
    lclkrslem1.h
    lclkrslem1.u
    lclkrslem1.k
    dvhlmod
    #
    wph
    cD
    cR
    c.x
    cF
    cG
    cB
    cU
    cX
    lclkrslem1.f
    lclkrslem1.r
    lclkrslem1.b
    lclkrslem1.d
    lclkrslem1.t
    @13
    lclkrslem1.x
    wph
    cG
    cF
    wcel
    #
    @9
    c.pe
    cfv
    @8
    wceq
    #
    @10
    wph
    @6
    @14
    @15
    @10
    w3a
    lclkrslem1.g
    cC
    cQ
    vf
    cF
    cG
    cL
    c.pe
    lclkrslem1.c
    lcfls1lem
    sylib
    #
    simp1d
    #
    ldualvscl
    lkrssv
    wph
    cD
    cR
    c.x
    cF
    cG
    cB
    cL
    cU
    cX
    lclkrslem1.r
    lclkrslem1.b
    lclkrslem1.f
    lclkrslem1.l
    lclkrslem1.d
    lclkrslem1.t
    wph
    cU
    cH
    cK
    cW
    lclkrslem1.h
    lclkrslem1.u
    lclkrslem1.k
    dvhlvec
    @17
    lclkrslem1.x
    lkrss
    cU
    cH
    cK
    c.pe
    @11
    cW
    @8
    @3
    lclkrslem1.h
    lclkrslem1.u
    @12
    lclkrslem1.o
    dochss
    syl3anc
    wph
    @14
    @15
    @10
    @16
    simp3d
    sstrd
    cC
    @2
    cQ
    vf
    cF
    @0
    cL
    c.pe
    lclkrslem1.c
    @5
    lcfls1c
    sylanbrc
end
