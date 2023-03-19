include "co.mm"
include "cpr.mm"
include "club.mm"
include "cfv.mm"
include "eqid.mm"
include "joinval.mm"
include "cop.mm"
include "cdm.mm"
include "wcel.mm"
include "joindef.mm"
include "mpbid.mm"
include "lubcl.mm"
include "eqeltrd.mm"

theorem joincl
  let wph: wff ph
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  assume joincl.b: |- B = ( Base ` K )
  assume joincl.j: |- .\/ = ( join ` K )
  assume joincl.k: |- ( ph -> K e. V )
  assume joincl.x: |- ( ph -> X e. B )
  assume joincl.y: |- ( ph -> Y e. B )
  assume joincl.e: |- ( ph -> <. X , Y >. e. dom .\/ )


  assert |- ( ph -> ( X .\/ Y ) e. B )

  proof
    wph
    cX
    cY
    c.or
    co
    cX
    cY
    cpr
    #
    cK
    club
    cfv
    #
    cfv
    cB
    wph
    @1
    c.or
    cK
    cV
    cB
    cX
    cY
    cB
    @1
    eqid
    #
    joincl.j
    joincl.k
    joincl.x
    joincl.y
    joinval
    wph
    cB
    @0
    @1
    cK
    cV
    joincl.b
    @2
    joincl.k
    wph
    cX
    cY
    cop
    c.or
    cdm
    wcel
    @0
    @1
    cdm
    wcel
    joincl.e
    wph
    @1
    c.or
    cK
    cV
    cB
    cX
    cY
    cB
    @2
    joincl.j
    joincl.k
    joincl.x
    joincl.y
    joindef
    mpbid
    lubcl
    eqeltrd
end
