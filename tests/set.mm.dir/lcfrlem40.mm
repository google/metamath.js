include "cv.mm"
include "wne.mm"
include "cpr.mm"
include "cfv.mm"
include "co.mm"
include "csn.mm"
include "cin.mm"
include "wrex.mm"
include "wcel.mm"
include "clsa.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "cbs.mm"
include "cdif.mm"
include "lcfrlem4.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "lcfrlem21.mm"
include "lsateln0.mm"
include "w3a.mm"
include "chlt.mm"
include "wa.mm"
include "3ad2ant1.mm"
include "wss.mm"
include "simp2.mm"
include "simp3.mm"
include "lcfrlem39.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem lcfrlem40
  let wph: wff ph
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cQ: class Q
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let cN: class N
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vi: setvar i
  let vk: setvar k
  let cI: class I
  let cJ: class J
  let vj: setvar j
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cV: class V
  assume lcfrlem38.h: |- H = ( LHyp ` K )
  assume lcfrlem38.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfrlem38.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfrlem38.p: |- .+ = ( +g ` U )
  assume lcfrlem38.f: |- F = ( LFnl ` U )
  assume lcfrlem38.l: |- L = ( LKer ` U )
  assume lcfrlem38.d: |- D = ( LDual ` U )
  assume lcfrlem38.q: |- Q = ( LSubSp ` D )
  assume lcfrlem38.c: |- C = { f e. ( LFnl ` U ) | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }
  assume lcfrlem38.e: |- E = U_ g e. G ( ._|_ ` ( L ` g ) )
  assume lcfrlem38.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfrlem38.g: |- ( ph -> G e. Q )
  assume lcfrlem38.gs: |- ( ph -> G C_ C )
  assume lcfrlem38.xe: |- ( ph -> X e. E )
  assume lcfrlem38.ye: |- ( ph -> Y e. E )
  assume lcfrlem38.z: |- .0. = ( 0g ` U )
  assume lcfrlem38.x: |- ( ph -> X =/= .0. )
  assume lcfrlem38.y: |- ( ph -> Y =/= .0. )
  assume lcfrlem38.sp: |- N = ( LSpan ` U )
  assume lcfrlem38.ne: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )

  disjoint N g
  disjoint D g
  disjoint G g
  disjoint f g
  disjoint L f
  disjoint L g
  disjoint ._|_ f
  disjoint ._|_ g
  disjoint .+ f
  disjoint .+ g
  disjoint U f
  disjoint U g
  disjoint X f
  disjoint X g
  disjoint Y f
  disjoint Y g
  disjoint .0. f
  disjoint .0. g
  disjoint g ph
  disjoint E i
  disjoint g i
  disjoint N i
  disjoint ._|_ i
  disjoint .+ i
  disjoint U i
  disjoint X i
  disjoint Y i
  disjoint .0. i
  disjoint i ph
  disjoint g k
  disjoint D k
  disjoint G k
  disjoint I g
  disjoint I k
  disjoint f k
  disjoint J f
  disjoint J g
  disjoint J k
  disjoint L k
  disjoint f j
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint g j
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint j k
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint ._|_ j
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint ._|_ k
  disjoint v w
  disjoint v x
  disjoint ._|_ v
  disjoint w x
  disjoint ._|_ w
  disjoint ._|_ x
  disjoint .+ j
  disjoint .+ k
  disjoint .+ v
  disjoint .+ w
  disjoint .+ x
  disjoint R f
  disjoint R k
  disjoint R v
  disjoint R x
  disjoint S g
  disjoint S k
  disjoint .x. f
  disjoint .x. k
  disjoint .x. v
  disjoint .x. w
  disjoint .x. x
  disjoint U j
  disjoint U k
  disjoint U v
  disjoint U w
  disjoint U x
  disjoint V f
  disjoint V g
  disjoint V v
  disjoint V x
  disjoint X k
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint Y k
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint .0. k
  disjoint .0. x
  disjoint k ph
  assert |- ( ph -> ( X .+ Y ) e. E )

  proof
    wph
    vi
    cv
    #
    c.0
    wne
    #
    vi
    cX
    cY
    cpr
    cN
    cfv
    cX
    cY
    c.pl
    co
    #
    csn
    c.pe
    cfv
    cin
    #
    wrex
    @2
    cE
    wcel
    #
    wph
    vi
    cU
    clsa
    cfv
    #
    @3
    cU
    c.0
    lcfrlem38.z
    @5
    eqid
    #
    wph
    cU
    cH
    cK
    cW
    lcfrlem38.h
    lcfrlem38.u
    lcfrlem38.k
    dvhlmod
    wph
    @5
    c.pl
    cU
    cH
    cK
    cN
    c.pe
    cU
    cbs
    cfv
    #
    cW
    cX
    cY
    c.0
    lcfrlem38.h
    lcfrlem38.o
    lcfrlem38.u
    @7
    eqid
    #
    lcfrlem38.p
    lcfrlem38.z
    lcfrlem38.sp
    @6
    lcfrlem38.k
    wph
    cX
    @7
    wcel
    cX
    c.0
    wne
    #
    cX
    @7
    c.0
    csn
    cdif
    #
    wcel
    wph
    cD
    cQ
    cU
    vg
    cE
    cG
    cH
    cK
    cL
    c.pe
    @7
    cW
    cX
    lcfrlem38.h
    lcfrlem38.o
    lcfrlem38.u
    @8
    lcfrlem38.l
    lcfrlem38.d
    lcfrlem38.q
    lcfrlem38.e
    lcfrlem38.k
    lcfrlem38.g
    lcfrlem38.xe
    lcfrlem4
    lcfrlem38.x
    cX
    @7
    c.0
    eldifsn
    sylanbrc
    wph
    cY
    @7
    wcel
    cY
    c.0
    wne
    #
    cY
    @10
    wcel
    wph
    cD
    cQ
    cU
    vg
    cE
    cG
    cH
    cK
    cL
    c.pe
    @7
    cW
    cY
    lcfrlem38.h
    lcfrlem38.o
    lcfrlem38.u
    @8
    lcfrlem38.l
    lcfrlem38.d
    lcfrlem38.q
    lcfrlem38.e
    lcfrlem38.k
    lcfrlem38.g
    lcfrlem38.ye
    lcfrlem4
    lcfrlem38.y
    cY
    @7
    c.0
    eldifsn
    sylanbrc
    lcfrlem38.ne
    lcfrlem21
    lsateln0
    wph
    @1
    @4
    vi
    @3
    wph
    @0
    @3
    wcel
    #
    @1
    w3a
    @3
    cC
    cD
    c.pl
    cQ
    cU
    vf
    vg
    cE
    cF
    cG
    cH
    @0
    cK
    cL
    cN
    c.pe
    cW
    cX
    cY
    c.0
    lcfrlem38.h
    lcfrlem38.o
    lcfrlem38.u
    lcfrlem38.p
    lcfrlem38.f
    lcfrlem38.l
    lcfrlem38.d
    lcfrlem38.q
    lcfrlem38.c
    lcfrlem38.e
    wph
    @12
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @1
    lcfrlem38.k
    3ad2ant1
    wph
    @12
    cG
    cQ
    wcel
    @1
    lcfrlem38.g
    3ad2ant1
    wph
    @12
    cG
    cC
    wss
    @1
    lcfrlem38.gs
    3ad2ant1
    wph
    @12
    cX
    cE
    wcel
    @1
    lcfrlem38.xe
    3ad2ant1
    wph
    @12
    cY
    cE
    wcel
    @1
    lcfrlem38.ye
    3ad2ant1
    lcfrlem38.z
    wph
    @12
    @9
    @1
    lcfrlem38.x
    3ad2ant1
    wph
    @12
    @11
    @1
    lcfrlem38.y
    3ad2ant1
    lcfrlem38.sp
    wph
    @12
    cX
    csn
    cN
    cfv
    cY
    csn
    cN
    cfv
    wne
    @1
    lcfrlem38.ne
    3ad2ant1
    @3
    eqid
    wph
    @12
    @1
    simp2
    wph
    @12
    @1
    simp3
    lcfrlem39
    rexlimdv3a
    mpd
end
