include "co.mm"
include "cxp.mm"
include "cdm.mm"
include "cinv.mm"
include "cfv.mm"
include "eqid.mm"
include "isoval.mm"
include "wss.mm"
include "invss.mm"
include "dmss.mm"
include "syl.mm"
include "eqsstrd.mm"
include "dmxpss.mm"
include "syl6ss.mm"

theorem isohom
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cH: class H
  let cI: class I
  let cX: class X
  let cY: class Y
  assume isohom.b: |- B = ( Base ` C )
  assume isohom.h: |- H = ( Hom ` C )
  assume isohom.i: |- I = ( Iso ` C )
  assume isohom.c: |- ( ph -> C e. Cat )
  assume isohom.x: |- ( ph -> X e. B )
  assume isohom.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X I Y ) C_ ( X H Y ) )

  proof
    wph
    cX
    cY
    cI
    co
    #
    cX
    cY
    cH
    co
    #
    cY
    cX
    cH
    co
    #
    cxp
    #
    cdm
    #
    @1
    wph
    @0
    cX
    cY
    cC
    cinv
    cfv
    #
    co
    #
    cdm
    #
    @4
    wph
    cB
    cC
    cI
    @5
    cX
    cY
    isohom.b
    @5
    eqid
    #
    isohom.c
    isohom.x
    isohom.y
    isohom.i
    isoval
    wph
    @6
    @3
    wss
    @7
    @4
    wss
    wph
    cB
    cC
    cH
    @5
    cX
    cY
    isohom.b
    @8
    isohom.c
    isohom.x
    isohom.y
    isohom.h
    invss
    @6
    @3
    dmss
    syl
    eqsstrd
    @1
    @2
    dmxpss
    syl6ss
end
