include "cba.mm"
include "cfv.mm"
include "cv.mm"
include "sspmval.mm"
include "nvmf.mm"
include "eqid.mm"
include "sspmlem.mm"

theorem sspm
  let cU: class U
  let cH: class H
  let cL: class L
  let cM: class M
  let cW: class W
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume sspm.y: |- Y = ( BaseSet ` W )
  assume sspm.m: |- M = ( -v ` U )
  assume sspm.l: |- L = ( -v ` W )
  assume sspm.h: |- H = ( SubSp ` U )


  assert |- ( ( U e. NrmCVec /\ W e. H ) -> L = ( M |` ( Y X. Y ) ) )

  proof
    vx
    vy
    cY
    cU
    cba
    cfv
    #
    cU
    cL
    cM
    cH
    cW
    cY
    sspm.y
    sspm.h
    vx
    cv
    vy
    cv
    cU
    cH
    cL
    cM
    cW
    cY
    sspm.y
    sspm.m
    sspm.l
    sspm.h
    sspmval
    cW
    cL
    cY
    sspm.y
    sspm.l
    nvmf
    cU
    cM
    @0
    @0
    eqid
    sspm.m
    nvmf
    sspmlem
end
