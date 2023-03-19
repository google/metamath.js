include "cur.mm"
include "cfv.mm"
include "cv.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt.mm"
include "cmps.mm"
include "co.mm"
include "cbs.mm"
include "csubrg.mm"
include "wcel.mm"
include "eqid.mm"
include "mplsubrg.mm"
include "mplval2.mm"
include "subrg1.mm"
include "syl.mm"
include "psr1.mm"
include "eqtr3d.mm"
include "syl5eq.mm"

theorem mpl1
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cP: class P
  let cR: class R
  let cU: class U
  let c.1: class .1.
  let vf: setvar f
  let cI: class I
  let cW: class W
  let c.0: class .0.
  assume mpl1.p: |- P = ( I mPoly R )
  assume mpl1.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume mpl1.z: |- .0. = ( 0g ` R )
  assume mpl1.o: |- .1. = ( 1r ` R )
  assume mpl1.u: |- U = ( 1r ` P )
  assume mpl1.i: |- ( ph -> I e. W )
  assume mpl1.r: |- ( ph -> R e. Ring )

  disjoint D x
  disjoint f x
  disjoint I f
  disjoint I x
  disjoint .1. x
  disjoint ph x
  disjoint R f
  disjoint R x
  disjoint W x
  disjoint .0. f
  disjoint .0. x
  assert |- ( ph -> U = ( x e. D |-> if ( x = ( I X. { 0 } ) , .1. , .0. ) ) )

  proof
    wph
    cU
    cP
    cur
    cfv
    #
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
    mpl1.u
    wph
    cI
    cR
    cmps
    co
    #
    cur
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
    csubrg
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
    mpl1.p
    @4
    eqid
    #
    mpl1.i
    mpl1.r
    mplsubrg
    @4
    @2
    cP
    @3
    cP
    cR
    @2
    @4
    cI
    mpl1.p
    @5
    @6
    mplval2
    @3
    eqid
    #
    subrg1
    syl
    wph
    vx
    cD
    cR
    @2
    @3
    c.1
    vf
    cI
    cW
    c.0
    @5
    mpl1.i
    mpl1.r
    mpl1.d
    mpl1.z
    mpl1.o
    @7
    psr1
    eqtr3d
    syl5eq
end
