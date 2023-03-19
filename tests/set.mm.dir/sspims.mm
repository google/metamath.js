include "cr.mm"
include "cv.mm"
include "sspimsval.mm"
include "imsdf.mm"
include "cba.mm"
include "cfv.mm"
include "eqid.mm"
include "sspmlem.mm"

theorem sspims
  let cC: class C
  let cD: class D
  let cU: class U
  let cH: class H
  let cW: class W
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume sspims.y: |- Y = ( BaseSet ` W )
  assume sspims.d: |- D = ( IndMet ` U )
  assume sspims.c: |- C = ( IndMet ` W )
  assume sspims.h: |- H = ( SubSp ` U )


  assert |- ( ( U e. NrmCVec /\ W e. H ) -> C = ( D |` ( Y X. Y ) ) )

  proof
    vx
    vy
    cr
    cr
    cU
    cC
    cD
    cH
    cW
    cY
    sspims.y
    sspims.h
    vx
    cv
    vy
    cv
    cC
    cD
    cU
    cH
    cW
    cY
    sspims.y
    sspims.d
    sspims.c
    sspims.h
    sspimsval
    cC
    cW
    cY
    sspims.y
    sspims.c
    imsdf
    cD
    cU
    cU
    cba
    cfv
    #
    @0
    eqid
    sspims.d
    imsdf
    sspmlem
end
