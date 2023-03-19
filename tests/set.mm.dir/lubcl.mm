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
include "lubelss.mm"
include "lubval.mm"
include "wreu.mm"
include "wcel.mm"
include "lubeu.mm"
include "riotacl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem lubcl
  let wph: wff ph
  let cB: class B
  let cS: class S
  let cU: class U
  let cK: class K
  let cV: class V
  let vx: setvar x
  let vz: setvar z
  let vy: setvar y
  assume lubcl.b: |- B = ( Base ` K )
  assume lubcl.u: |- U = ( lub ` K )
  assume lubcl.k: |- ( ph -> K e. V )
  assume lubcl.s: |- ( ph -> S e. dom U )


  assert |- ( ph -> ( U ` S ) e. B )

  proof
    wph
    cS
    cU
    cfv
    vy
    cv
    #
    vx
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
    @0
    vz
    cv
    #
    @2
    wbr
    vy
    cS
    wral
    @1
    @3
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
    cU
    cK
    @2
    cV
    lubcl.b
    @2
    eqid
    #
    lubcl.u
    @4
    biid
    #
    lubcl.k
    wph
    cB
    cS
    cU
    cK
    @2
    cV
    lubcl.b
    @6
    lubcl.u
    lubcl.k
    lubcl.s
    lubelss
    lubval
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
    cU
    cK
    @2
    cV
    lubcl.b
    @6
    lubcl.u
    @7
    lubcl.k
    lubcl.s
    lubeu
    @4
    vx
    cB
    riotacl
    syl
    eqeltrd
end
