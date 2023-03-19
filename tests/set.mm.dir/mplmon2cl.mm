include "cv.mm"
include "wceq.mm"
include "cur.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "cvsca.mm"
include "co.mm"
include "eqid.mm"
include "mplmon2.mm"
include "clmod.mm"
include "wcel.mm"
include "csca.mm"
include "cbs.mm"
include "crg.mm"
include "mpllmod.mm"
include "syl2anc.mm"
include "mplsca.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eleqtrd.mm"
include "mplmon.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"

theorem mplmon2cl
  let wph: wff ph
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let vf: setvar f
  let cI: class I
  let cK: class K
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume mplmon2cl.p: |- P = ( I mPoly R )
  assume mplmon2cl.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume mplmon2cl.z: |- .0. = ( 0g ` R )
  assume mplmon2cl.c: |- C = ( Base ` R )
  assume mplmon2cl.i: |- ( ph -> I e. W )
  assume mplmon2cl.r: |- ( ph -> R e. Ring )
  assume mplmon2cl.b: |- B = ( Base ` P )
  assume mplmon2cl.x: |- ( ph -> X e. C )
  assume mplmon2cl.k: |- ( ph -> K e. D )

  disjoint ph y
  disjoint C y
  disjoint D y
  disjoint I f
  disjoint K f
  disjoint K y
  disjoint f y
  disjoint R y
  disjoint X y
  disjoint .0. y
  assert |- ( ph -> ( y e. D |-> if ( y = K , X , .0. ) ) e. B )

  proof
    wph
    cX
    vy
    cD
    vy
    cv
    cK
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
    cP
    cvsca
    cfv
    #
    co
    #
    vy
    cD
    @0
    cX
    c.0
    cif
    cmpt
    cB
    wph
    vy
    cC
    cD
    cP
    cR
    @3
    @1
    vf
    cI
    cK
    cW
    cX
    c.0
    mplmon2cl.p
    @3
    eqid
    #
    mplmon2cl.d
    @1
    eqid
    #
    mplmon2cl.z
    mplmon2cl.c
    mplmon2cl.i
    mplmon2cl.r
    mplmon2cl.k
    mplmon2cl.x
    mplmon2
    wph
    cP
    clmod
    wcel
    #
    cX
    cP
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    @2
    cB
    wcel
    @4
    cB
    wcel
    wph
    cI
    cW
    wcel
    cR
    crg
    wcel
    @7
    mplmon2cl.i
    mplmon2cl.r
    cP
    cR
    cI
    cW
    mplmon2cl.p
    mpllmod
    syl2anc
    wph
    cX
    cC
    @9
    mplmon2cl.x
    wph
    cC
    cR
    cbs
    cfv
    @9
    mplmon2cl.c
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
    mplmon2cl.p
    mplmon2cl.i
    mplmon2cl.r
    mplsca
    fveq2d
    syl5eq
    eleqtrd
    wph
    vy
    cB
    cD
    cP
    cR
    @1
    vf
    cI
    cW
    cK
    c.0
    mplmon2cl.p
    mplmon2cl.b
    mplmon2cl.z
    @6
    mplmon2cl.d
    mplmon2cl.i
    mplmon2cl.r
    mplmon2cl.k
    mplmon
    cX
    @3
    @8
    @9
    cB
    cP
    @2
    mplmon2cl.b
    @8
    eqid
    @5
    @9
    eqid
    lmodvscl
    syl3anc
    eqeltrrd
end
