include "csca.mm"
include "cfv.mm"
include "cld.mm"
include "cv.mm"
include "clk.mm"
include "coch.mm"
include "wceq.mm"
include "clfn.mm"
include "crab.mm"
include "cress.mm"
include "co.mm"
include "chlt.mm"
include "eqid.mm"
include "lcdval.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "rabex.mm"
include "resssca.mm"
include "ax-mp.mm"
include "syl6eqr.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "ldualsca.mm"
include "eqtrd.mm"
include "syl5eq.mm"

theorem lcdsca
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cU: class U
  let cF: class F
  let cH: class H
  let cK: class K
  let cO: class O
  let cW: class W
  let vf: setvar f
  assume lcdsca.h: |- H = ( LHyp ` K )
  assume lcdsca.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdsca.f: |- F = ( Scalar ` U )
  assume lcdsca.o: |- O = ( oppR ` F )
  assume lcdsca.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdsca.r: |- R = ( Scalar ` C )
  assume lcdsca.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> R = O )

  proof
    wph
    cR
    cC
    csca
    cfv
    #
    cO
    lcdsca.r
    wph
    @0
    cU
    cld
    cfv
    #
    csca
    cfv
    #
    cO
    wph
    @0
    @1
    vf
    cv
    cU
    clk
    cfv
    #
    cfv
    #
    cW
    cK
    coch
    cfv
    cfv
    #
    cfv
    @5
    cfv
    @4
    wceq
    #
    vf
    cU
    clfn
    cfv
    #
    crab
    #
    cress
    co
    #
    csca
    cfv
    #
    @2
    wph
    cC
    @9
    csca
    wph
    cC
    @1
    cU
    vf
    @7
    cH
    cK
    @3
    @5
    cW
    chlt
    lcdsca.h
    @5
    eqid
    lcdsca.c
    lcdsca.u
    @7
    eqid
    @3
    eqid
    @1
    eqid
    #
    lcdsca.k
    lcdval
    fveq2d
    @8
    cvv
    wcel
    @2
    @10
    wceq
    @6
    vf
    @7
    cU
    clfn
    fvex
    rabex
    @8
    @2
    @1
    @9
    cvv
    @9
    eqid
    @2
    eqid
    #
    resssca
    ax-mp
    syl6eqr
    wph
    @1
    @2
    cF
    cO
    cU
    clmod
    lcdsca.f
    lcdsca.o
    @11
    @12
    wph
    cU
    cH
    cK
    cW
    lcdsca.h
    lcdsca.u
    lcdsca.k
    dvhlmod
    ldualsca
    eqtrd
    syl5eq
end
