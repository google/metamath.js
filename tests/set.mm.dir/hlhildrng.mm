include "cedring.mm"
include "cfv.mm"
include "cdr.mm"
include "wcel.mm"
include "chlt.mm"
include "wa.mm"
include "eqid.mm"
include "erngdv.mm"
include "syl.mm"
include "cbs.mm"
include "eqidd.mm"
include "hlhilsbase.mm"
include "cv.mm"
include "cplusg.mm"
include "hlhilsplus.mm"
include "oveqdr.mm"
include "cmulr.mm"
include "hlhilsmul.mm"
include "drngpropd.mm"
include "mpbid.mm"

theorem hlhildrng
  let wph: wff ph
  let cR: class R
  let cU: class U
  let cH: class H
  let cK: class K
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  assume hlhillvec.h: |- H = ( LHyp ` K )
  assume hlhillvec.u: |- U = ( ( HLHil ` K ) ` W )
  assume hlhillvec.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hlhildrng.r: |- R = ( Scalar ` U )


  assert |- ( ph -> R e. DivRing )

  proof
    wph
    cW
    cK
    cedring
    cfv
    cfv
    #
    cdr
    wcel
    #
    cR
    cdr
    wcel
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @1
    hlhillvec.k
    @0
    cH
    cK
    cW
    hlhillvec.h
    @0
    eqid
    #
    erngdv
    syl
    wph
    vx
    vy
    @0
    cbs
    cfv
    #
    @0
    cR
    wph
    @3
    eqidd
    wph
    @3
    cR
    cU
    @0
    cH
    cK
    cW
    hlhillvec.h
    @2
    hlhillvec.u
    hlhildrng.r
    hlhillvec.k
    @3
    eqid
    hlhilsbase
    wph
    vx
    cv
    @3
    wcel
    vy
    cv
    @3
    wcel
    wa
    #
    vx
    vy
    @0
    cplusg
    cfv
    #
    cR
    cplusg
    cfv
    wph
    @5
    cR
    cU
    @0
    cH
    cK
    cW
    hlhillvec.h
    @2
    hlhillvec.u
    hlhildrng.r
    hlhillvec.k
    @5
    eqid
    hlhilsplus
    oveqdr
    wph
    @4
    vx
    vy
    @0
    cmulr
    cfv
    #
    cR
    cmulr
    cfv
    wph
    cR
    @6
    cU
    @0
    cH
    cK
    cW
    hlhillvec.h
    @2
    hlhillvec.u
    hlhildrng.r
    hlhillvec.k
    @6
    eqid
    hlhilsmul
    oveqdr
    drngpropd
    mpbid
end
