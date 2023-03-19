include "csca.mm"
include "cfv.mm"
include "cplusg.mm"
include "cof.mm"
include "co.mm"
include "eqid.mm"
include "lfladdcom.mm"
include "clmod.mm"
include "ldualvadd.mm"
include "3eqtr4d.mm"

theorem ldualvaddcom
  let wph: wff ph
  let cD: class D
  let c.pl: class .+
  let cF: class F
  let cW: class W
  let cX: class X
  let cY: class Y
  assume ldualvaddcom.f: |- F = ( LFnl ` W )
  assume ldualvaddcom.d: |- D = ( LDual ` W )
  assume ldualvaddcom.p: |- .+ = ( +g ` D )
  assume ldualvaddcom.w: |- ( ph -> W e. LMod )
  assume ldualvaddcom.x: |- ( ph -> X e. F )
  assume ldualvaddcom.y: |- ( ph -> Y e. F )


  assert |- ( ph -> ( X .+ Y ) = ( Y .+ X ) )

  proof
    wph
    cX
    cY
    cW
    csca
    cfv
    #
    cplusg
    cfv
    #
    cof
    #
    co
    cY
    cX
    @2
    co
    cX
    cY
    c.pl
    co
    cY
    cX
    c.pl
    co
    wph
    @1
    @0
    cF
    cX
    cY
    cW
    @0
    eqid
    #
    @1
    eqid
    #
    ldualvaddcom.f
    ldualvaddcom.w
    ldualvaddcom.x
    ldualvaddcom.y
    lfladdcom
    wph
    cD
    @1
    c.pl
    @0
    cF
    cX
    cY
    cW
    clmod
    ldualvaddcom.f
    @3
    @4
    ldualvaddcom.d
    ldualvaddcom.p
    ldualvaddcom.w
    ldualvaddcom.x
    ldualvaddcom.y
    ldualvadd
    wph
    cD
    @1
    c.pl
    @0
    cF
    cY
    cX
    cW
    clmod
    ldualvaddcom.f
    @3
    @4
    ldualvaddcom.d
    ldualvaddcom.p
    ldualvaddcom.w
    ldualvaddcom.y
    ldualvaddcom.x
    ldualvadd
    3eqtr4d
end
