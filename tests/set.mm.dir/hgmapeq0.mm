include "cfv.mm"
include "wceq.mm"
include "hgmapval0.mm"
include "eqeq2d.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "lmod0cl.mm"
include "syl.mm"
include "hgmap11.mm"
include "bitr3d.mm"

theorem hgmapeq0
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cU: class U
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume hgmapeq0.h: |- H = ( LHyp ` K )
  assume hgmapeq0.u: |- U = ( ( DVecH ` K ) ` W )
  assume hgmapeq0.r: |- R = ( Scalar ` U )
  assume hgmapeq0.b: |- B = ( Base ` R )
  assume hgmapeq0.o: |- .0. = ( 0g ` R )
  assume hgmapeq0.g: |- G = ( ( HGMap ` K ) ` W )
  assume hgmapeq0.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hgmapeq0.x: |- ( ph -> X e. B )


  assert |- ( ph -> ( ( G ` X ) = .0. <-> X = .0. ) )

  proof
    wph
    cX
    cG
    cfv
    #
    c.0
    cG
    cfv
    #
    wceq
    @0
    c.0
    wceq
    cX
    c.0
    wceq
    wph
    @1
    c.0
    @0
    wph
    cR
    cU
    cG
    cH
    cK
    cW
    c.0
    hgmapeq0.h
    hgmapeq0.u
    hgmapeq0.r
    hgmapeq0.o
    hgmapeq0.g
    hgmapeq0.k
    hgmapval0
    eqeq2d
    wph
    cB
    cR
    cU
    cG
    cH
    cK
    cW
    cX
    c.0
    hgmapeq0.h
    hgmapeq0.u
    hgmapeq0.r
    hgmapeq0.b
    hgmapeq0.g
    hgmapeq0.k
    hgmapeq0.x
    wph
    cU
    clmod
    wcel
    c.0
    cB
    wcel
    wph
    cU
    cH
    cK
    cW
    hgmapeq0.h
    hgmapeq0.u
    hgmapeq0.k
    dvhlmod
    cR
    cB
    cU
    c.0
    hgmapeq0.r
    hgmapeq0.b
    hgmapeq0.o
    lmod0cl
    syl
    hgmap11
    bitr3d
end
