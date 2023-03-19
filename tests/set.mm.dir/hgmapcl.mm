include "cfv.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "chdma.mm"
include "clcd.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "crio.mm"
include "chlt.mm"
include "eqid.mm"
include "hgmapval.mm"
include "wreu.mm"
include "wcel.mm"
include "hdmap14lem15.mm"
include "riotacl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem hgmapcl
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let vg: setvar g
  let vx: setvar x
  assume hgmapcl.h: |- H = ( LHyp ` K )
  assume hgmapcl.u: |- U = ( ( DVecH ` K ) ` W )
  assume hgmapcl.r: |- R = ( Scalar ` U )
  assume hgmapcl.b: |- B = ( Base ` R )
  assume hgmapcl.g: |- G = ( ( HGMap ` K ) ` W )
  assume hgmapcl.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hgmapcl.f: |- ( ph -> F e. B )


  assert |- ( ph -> ( G ` F ) e. B )

  proof
    wph
    cF
    cG
    cfv
    cF
    vx
    cv
    #
    cU
    cvsca
    cfv
    #
    co
    cW
    cK
    chdma
    cfv
    cfv
    #
    cfv
    vg
    cv
    @0
    @2
    cfv
    cW
    cK
    clcd
    cfv
    cfv
    #
    cvsca
    cfv
    #
    co
    wceq
    vx
    cU
    cbs
    cfv
    #
    wral
    #
    vg
    cB
    crio
    #
    cB
    wph
    vg
    vx
    cB
    @3
    cR
    @4
    @1
    cU
    cH
    cG
    cK
    @2
    @5
    cW
    cF
    chlt
    hgmapcl.h
    hgmapcl.u
    @5
    eqid
    #
    @1
    eqid
    #
    hgmapcl.r
    hgmapcl.b
    @3
    eqid
    #
    @4
    eqid
    #
    @2
    eqid
    #
    hgmapcl.g
    hgmapcl.k
    hgmapcl.f
    hgmapval
    wph
    @6
    vg
    cB
    wreu
    @7
    cB
    wcel
    wph
    vx
    cB
    @3
    cR
    @2
    @4
    @1
    cU
    vg
    cF
    cH
    cK
    @5
    cW
    hgmapcl.h
    hgmapcl.u
    @8
    @9
    hgmapcl.r
    hgmapcl.b
    @10
    @11
    @12
    hgmapcl.k
    hgmapcl.f
    hdmap14lem15
    @6
    vg
    cB
    riotacl
    syl
    eqeltrd
end
