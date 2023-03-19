include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "wreu.mm"
include "cdm.mm"
include "wcel.mm"
include "biid.mm"
include "lubeldm.mm"
include "mpbid.mm"
include "simpld.mm"

theorem lubelss
  let wph: wff ph
  let cB: class B
  let cS: class S
  let cU: class U
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let vx: setvar x
  let vz: setvar z
  let vy: setvar y
  assume lubs.b: |- B = ( Base ` K )
  assume lubs.l: |- .<_ = ( le ` K )
  assume lubs.u: |- U = ( lub ` K )
  assume lubs.k: |- ( ph -> K e. V )
  assume lubs.s: |- ( ph -> S e. dom U )


  assert |- ( ph -> S C_ B )

  proof
    wph
    cS
    cB
    wss
    #
    vy
    cv
    #
    vx
    cv
    #
    c.le
    wbr
    vy
    cS
    wral
    @1
    vz
    cv
    #
    c.le
    wbr
    vy
    cS
    wral
    @2
    @3
    c.le
    wbr
    wi
    vz
    cB
    wral
    wa
    #
    vx
    cB
    wreu
    #
    wph
    cS
    cU
    cdm
    wcel
    @0
    @5
    wa
    lubs.s
    wph
    @4
    vx
    vy
    vz
    cB
    cS
    cU
    cK
    c.le
    cV
    lubs.b
    lubs.l
    lubs.u
    @4
    biid
    lubs.k
    lubeldm
    mpbid
    simpld
end
