include "cdvh.mm"
include "cfv.mm"
include "csca.mm"
include "cbs.mm"
include "cplusg.mm"
include "cmulr.mm"
include "chg.mm"
include "eqid.mm"
include "hlhilsrnglem.mm"

theorem hlhilsrng
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


  assert |- ( ph -> R e. *Ring )

  proof
    wph
    cW
    cK
    cdvh
    cfv
    cfv
    #
    csca
    cfv
    #
    cbs
    cfv
    #
    @1
    cplusg
    cfv
    #
    cR
    @1
    @1
    cmulr
    cfv
    #
    cU
    cW
    cK
    chg
    cfv
    cfv
    #
    cH
    cK
    @0
    cW
    hlhillvec.h
    hlhillvec.u
    hlhillvec.k
    hlhildrng.r
    @0
    eqid
    @1
    eqid
    @2
    eqid
    @3
    eqid
    @4
    eqid
    @5
    eqid
    hlhilsrnglem
end
