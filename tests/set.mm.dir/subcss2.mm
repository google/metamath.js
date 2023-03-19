include "co.mm"
include "chomf.mm"
include "cfv.mm"
include "eqid.mm"
include "subcssc.mm"
include "ssc2.mm"
include "cbs.mm"
include "subcss1.mm"
include "sseldd.mm"
include "homfval.mm"
include "sseqtrd.mm"

theorem subcss2
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cH: class H
  let cJ: class J
  let cX: class X
  let cY: class Y
  assume subcss1.1: |- ( ph -> J e. ( Subcat ` C ) )
  assume subcss1.2: |- ( ph -> J Fn ( S X. S ) )
  assume subcss2.h: |- H = ( Hom ` C )
  assume subcss2.x: |- ( ph -> X e. S )
  assume subcss2.y: |- ( ph -> Y e. S )


  assert |- ( ph -> ( X J Y ) C_ ( X H Y ) )

  proof
    wph
    cX
    cY
    cJ
    co
    cX
    cY
    cC
    chomf
    cfv
    #
    co
    cX
    cY
    cH
    co
    wph
    cS
    cJ
    @0
    cX
    cY
    subcss1.2
    wph
    cC
    @0
    cJ
    subcss1.1
    @0
    eqid
    #
    subcssc
    subcss2.x
    subcss2.y
    ssc2
    wph
    cC
    cbs
    cfv
    #
    cC
    @0
    cH
    cX
    cY
    @1
    @2
    eqid
    #
    subcss2.h
    wph
    cS
    @2
    cX
    wph
    @2
    cC
    cS
    cJ
    subcss1.1
    subcss1.2
    @3
    subcss1
    #
    subcss2.x
    sseldd
    wph
    cS
    @2
    cY
    @4
    subcss2.y
    sseldd
    homfval
    sseqtrd
end
