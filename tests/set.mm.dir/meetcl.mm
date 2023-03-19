include "co.mm"
include "cpr.mm"
include "cglb.mm"
include "cfv.mm"
include "eqid.mm"
include "meetval.mm"
include "cop.mm"
include "cdm.mm"
include "wcel.mm"
include "meetdef.mm"
include "mpbid.mm"
include "glbcl.mm"
include "eqeltrd.mm"

theorem meetcl
  let wph: wff ph
  let cB: class B
  let cK: class K
  let c.an: class ./\
  let cV: class V
  let cX: class X
  let cY: class Y
  assume meetcl.b: |- B = ( Base ` K )
  assume meetcl.m: |- ./\ = ( meet ` K )
  assume meetcl.k: |- ( ph -> K e. V )
  assume meetcl.x: |- ( ph -> X e. B )
  assume meetcl.y: |- ( ph -> Y e. B )
  assume meetcl.e: |- ( ph -> <. X , Y >. e. dom ./\ )


  assert |- ( ph -> ( X ./\ Y ) e. B )

  proof
    wph
    cX
    cY
    c.an
    co
    cX
    cY
    cpr
    #
    cK
    cglb
    cfv
    #
    cfv
    cB
    wph
    @1
    cK
    c.an
    cV
    cB
    cX
    cY
    cB
    @1
    eqid
    #
    meetcl.m
    meetcl.k
    meetcl.x
    meetcl.y
    meetval
    wph
    cB
    @0
    @1
    cK
    cV
    meetcl.b
    @2
    meetcl.k
    wph
    cX
    cY
    cop
    c.an
    cdm
    wcel
    @0
    @1
    cdm
    wcel
    meetcl.e
    wph
    @1
    cK
    c.an
    cV
    cB
    cX
    cY
    cB
    @2
    meetcl.m
    meetcl.k
    meetcl.x
    meetcl.y
    meetdef
    mpbid
    glbcl
    eqeltrd
end
