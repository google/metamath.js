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
include "glbeldm.mm"
include "mpbid.mm"
include "simpld.mm"

theorem glbelss
  let wph: wff ph
  let cB: class B
  let cS: class S
  let cG: class G
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let vx: setvar x
  let vz: setvar z
  let vy: setvar y
  assume glbs.b: |- B = ( Base ` K )
  assume glbs.l: |- .<_ = ( le ` K )
  assume glbs.g: |- G = ( glb ` K )
  assume glbs.k: |- ( ph -> K e. V )
  assume glbs.s: |- ( ph -> S e. dom G )


  assert |- ( ph -> S C_ B )

  proof
    wph
    cS
    cB
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    c.le
    wbr
    vy
    cS
    wral
    vz
    cv
    #
    @2
    c.le
    wbr
    vy
    cS
    wral
    @3
    @1
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
    cG
    cdm
    wcel
    @0
    @5
    wa
    glbs.s
    wph
    @4
    vx
    vy
    vz
    cB
    cS
    cG
    cK
    c.le
    cV
    glbs.b
    glbs.l
    glbs.g
    @4
    biid
    glbs.k
    glbeldm
    mpbid
    simpld
end
