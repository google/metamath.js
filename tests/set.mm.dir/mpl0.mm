include "c0g.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cmps.mm"
include "co.mm"
include "cbs.mm"
include "csubg.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "mplsubg.mm"
include "mplval2.mm"
include "subg0.mm"
include "syl.mm"
include "psr0.mm"
include "eqtr3d.mm"
include "syl5eq.mm"

theorem mpl0
  let wph: wff ph
  let cD: class D
  let cP: class P
  let cR: class R
  let vf: setvar f
  let cI: class I
  let cO: class O
  let cW: class W
  let c.0: class .0.
  assume mpl0.p: |- P = ( I mPoly R )
  assume mpl0.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume mpl0.o: |- O = ( 0g ` R )
  assume mpl0.z: |- .0. = ( 0g ` P )
  assume mpl0.i: |- ( ph -> I e. W )
  assume mpl0.r: |- ( ph -> R e. Grp )

  disjoint I f
  assert |- ( ph -> .0. = ( D X. { O } ) )

  proof
    wph
    c.0
    cP
    c0g
    cfv
    #
    cD
    cO
    csn
    cxp
    #
    mpl0.z
    wph
    cI
    cR
    cmps
    co
    #
    c0g
    cfv
    #
    @0
    @1
    wph
    cP
    cbs
    cfv
    #
    @2
    csubg
    cfv
    wcel
    @3
    @0
    wceq
    wph
    cP
    cR
    @2
    @4
    cI
    cW
    @2
    eqid
    #
    mpl0.p
    @4
    eqid
    #
    mpl0.i
    mpl0.r
    mplsubg
    @4
    @2
    cP
    @3
    cP
    cR
    @2
    @4
    cI
    mpl0.p
    @5
    @6
    mplval2
    @3
    eqid
    #
    subg0
    syl
    wph
    cD
    cR
    @2
    vf
    cI
    cO
    cW
    @3
    @5
    mpl0.i
    mpl0.r
    mpl0.d
    mpl0.o
    @7
    psr0
    eqtr3d
    syl5eq
end
