include "cfv.mm"
include "cur.mm"
include "cvsca.mm"
include "co.mm"
include "cv.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt.mm"
include "csca.mm"
include "cbs.mm"
include "wcel.mm"
include "crg.mm"
include "mplsca.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eleqtrd.mm"
include "eqid.mm"
include "asclval.mm"
include "syl.mm"
include "mpl1.mm"
include "oveq2d.mm"
include "psrbag0.mm"
include "mplmon2.mm"
include "3eqtrd.mm"

theorem mplascl
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let vf: setvar f
  let cI: class I
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume mplascl.p: |- P = ( I mPoly R )
  assume mplascl.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume mplascl.z: |- .0. = ( 0g ` R )
  assume mplascl.b: |- B = ( Base ` R )
  assume mplascl.a: |- A = ( algSc ` P )
  assume mplascl.i: |- ( ph -> I e. W )
  assume mplascl.r: |- ( ph -> R e. Ring )
  assume mplascl.x: |- ( ph -> X e. B )

  disjoint ph y
  disjoint B y
  disjoint D y
  disjoint I f
  disjoint I y
  disjoint f y
  disjoint R f
  disjoint R y
  disjoint W y
  disjoint X y
  disjoint .0. f
  disjoint .0. y
  assert |- ( ph -> ( A ` X ) = ( y e. D |-> if ( y = ( I X. { 0 } ) , X , .0. ) ) )

  proof
    wph
    cX
    cA
    cfv
    #
    cX
    cP
    cur
    cfv
    #
    cP
    cvsca
    cfv
    #
    co
    #
    cX
    vy
    cD
    vy
    cv
    cI
    cc0
    csn
    cxp
    #
    wceq
    #
    cR
    cur
    cfv
    #
    c.0
    cif
    cmpt
    #
    @2
    co
    vy
    cD
    @5
    cX
    c.0
    cif
    cmpt
    wph
    cX
    cP
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    @0
    @3
    wceq
    wph
    cX
    cB
    @9
    mplascl.x
    wph
    cB
    cR
    cbs
    cfv
    @9
    mplascl.b
    wph
    cR
    @8
    cbs
    wph
    cP
    cR
    cI
    cW
    crg
    mplascl.p
    mplascl.i
    mplascl.r
    mplsca
    fveq2d
    syl5eq
    eleqtrd
    cA
    @2
    @1
    @8
    @9
    cP
    cX
    mplascl.a
    @8
    eqid
    @9
    eqid
    @2
    eqid
    #
    @1
    eqid
    #
    asclval
    syl
    wph
    @1
    @7
    cX
    @2
    wph
    vy
    cD
    cP
    cR
    @1
    @6
    vf
    cI
    cW
    c.0
    mplascl.p
    mplascl.d
    mplascl.z
    @6
    eqid
    #
    @11
    mplascl.i
    mplascl.r
    mpl1
    oveq2d
    wph
    vy
    cB
    cD
    cP
    cR
    @2
    @6
    vf
    cI
    @4
    cW
    cX
    c.0
    mplascl.p
    @10
    mplascl.d
    @12
    mplascl.z
    mplascl.b
    mplascl.i
    mplascl.r
    wph
    cI
    cW
    wcel
    @4
    cD
    wcel
    mplascl.i
    cD
    vf
    cI
    cW
    mplascl.d
    psrbag0
    syl
    mplascl.x
    mplmon2
    3eqtrd
end
