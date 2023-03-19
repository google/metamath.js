include "cv.mm"
include "cfv.mm"
include "weq.mm"
include "cur.mm"
include "cif.mm"
include "cmpt.mm"
include "cvsca.mm"
include "co.mm"
include "cgsu.mm"
include "eqid.mm"
include "mplcoe1.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "adantr.mm"
include "crg.mm"
include "simpr.mm"
include "mplelf.mm"
include "ffvelrnda.mm"
include "mplmon2.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem mplcoe4
  let wph: wff ph
  let vy: setvar y
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let vf: setvar f
  let vk: setvar k
  let cI: class I
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume mplcoe4.p: |- P = ( I mPoly R )
  assume mplcoe4.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume mplcoe4.z: |- .0. = ( 0g ` R )
  assume mplcoe4.b: |- B = ( Base ` P )
  assume mplcoe4.i: |- ( ph -> I e. W )
  assume mplcoe4.r: |- ( ph -> R e. Ring )
  assume mplcoe4.x: |- ( ph -> X e. B )

  disjoint k ph
  disjoint ph y
  disjoint k y
  disjoint B k
  disjoint D k
  disjoint D y
  disjoint I f
  disjoint I k
  disjoint I y
  disjoint f k
  disjoint f y
  disjoint P k
  disjoint P y
  disjoint R f
  disjoint R k
  disjoint R y
  disjoint W y
  disjoint W k
  disjoint X f
  disjoint X k
  disjoint X y
  disjoint .0. f
  disjoint .0. k
  disjoint .0. y
  assert |- ( ph -> X = ( P gsum ( k e. D |-> ( y e. D |-> if ( y = k , ( X ` k ) , .0. ) ) ) ) )

  proof
    wph
    cX
    cP
    vk
    cD
    vk
    cv
    #
    cX
    cfv
    #
    vy
    cD
    vy
    vk
    weq
    #
    cR
    cur
    cfv
    #
    c.0
    cif
    cmpt
    cP
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    cP
    vk
    cD
    vy
    cD
    @2
    @1
    c.0
    cif
    cmpt
    #
    cmpt
    #
    cgsu
    co
    wph
    vy
    cB
    cD
    cP
    cR
    @4
    @3
    vf
    vk
    cI
    cW
    cX
    c.0
    mplcoe4.p
    mplcoe4.d
    mplcoe4.z
    @3
    eqid
    #
    mplcoe4.i
    mplcoe4.b
    @4
    eqid
    #
    mplcoe4.r
    mplcoe4.x
    mplcoe1
    wph
    @6
    @8
    cP
    cgsu
    wph
    vk
    cD
    @5
    @7
    wph
    @0
    cD
    wcel
    #
    wa
    vy
    cR
    cbs
    cfv
    #
    cD
    cP
    cR
    @4
    @3
    vf
    cI
    @0
    cW
    @1
    c.0
    mplcoe4.p
    @10
    mplcoe4.d
    @9
    mplcoe4.z
    @12
    eqid
    #
    wph
    cI
    cW
    wcel
    @11
    mplcoe4.i
    adantr
    wph
    cR
    crg
    wcel
    @11
    mplcoe4.r
    adantr
    wph
    @11
    simpr
    wph
    cD
    @12
    @0
    cX
    wph
    cB
    cD
    cP
    cR
    vf
    cI
    @12
    cX
    mplcoe4.p
    @13
    mplcoe4.b
    mplcoe4.d
    mplcoe4.x
    mplelf
    ffvelrnda
    mplmon2
    mpteq2dva
    oveq2d
    eqtrd
end
