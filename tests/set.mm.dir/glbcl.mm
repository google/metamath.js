include "cfv.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "crio.mm"
include "eqid.mm"
include "biid.mm"
include "glbelss.mm"
include "glbval.mm"
include "wreu.mm"
include "wcel.mm"
include "glbeu.mm"
include "riotacl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem glbcl
  let wph: wff ph
  let cB: class B
  let cS: class S
  let cG: class G
  let cK: class K
  let cV: class V
  let vx: setvar x
  let vz: setvar z
  let vy: setvar y
  assume glbc.b: |- B = ( Base ` K )
  assume glbc.g: |- G = ( glb ` K )
  assume glbc.k: |- ( ph -> K e. V )
  assume glbc.s: |- ( ph -> S e. dom G )


  assert |- ( ph -> ( G ` S ) e. B )

  proof
    wph
    cS
    cG
    cfv
    vx
    cv
    #
    vy
    cv
    #
    cK
    cple
    cfv
    #
    wbr
    vy
    cS
    wral
    vz
    cv
    #
    @1
    @2
    wbr
    vy
    cS
    wral
    @3
    @0
    @2
    wbr
    wi
    vz
    cB
    wral
    wa
    #
    vx
    cB
    crio
    #
    cB
    wph
    @4
    vx
    vy
    vz
    cB
    cS
    cG
    cK
    @2
    cV
    glbc.b
    @2
    eqid
    #
    glbc.g
    @4
    biid
    #
    glbc.k
    wph
    cB
    cS
    cG
    cK
    @2
    cV
    glbc.b
    @6
    glbc.g
    glbc.k
    glbc.s
    glbelss
    glbval
    wph
    @4
    vx
    cB
    wreu
    @5
    cB
    wcel
    wph
    @4
    vx
    vy
    vz
    cB
    cS
    cG
    cK
    @2
    cV
    glbc.b
    @6
    glbc.g
    @7
    glbc.k
    glbc.s
    glbeu
    @4
    vx
    cB
    riotacl
    syl
    eqeltrd
end
