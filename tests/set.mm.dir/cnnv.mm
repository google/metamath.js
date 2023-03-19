include "cmul.mm"
include "caddc.mm"
include "cabs.mm"
include "cc.mm"
include "cc0.mm"
include "cablo.mm"
include "wcel.mm"
include "cgr.mm"
include "cnaddabloOLD.mm"
include "ablogrpo.mm"
include "ax-mp.mm"
include "cxp.mm"
include "ax-addf.mm"
include "fdmi.mm"
include "grporn.mm"
include "cnidOLD.mm"
include "cncvcOLD.mm"
include "absf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "abs00.mm"
include "biimpa.mm"
include "absmul.mm"
include "abstri.mm"
include "isnvi.mm"

theorem cnnv
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  assume cnnv.6: |- U = <. <. + , x. >. , abs >.


  assert |- U e. NrmCVec

  proof
    vx
    vy
    cmul
    cU
    caddc
    cabs
    cc
    cc0
    caddc
    cc
    caddc
    cablo
    wcel
    caddc
    cgr
    wcel
    cnaddabloOLD
    caddc
    ablogrpo
    ax-mp
    cc
    cc
    cxp
    cc
    caddc
    ax-addf
    fdmi
    grporn
    cnidOLD
    cncvcOLD
    absf
    vx
    cv
    #
    cc
    wcel
    @0
    cabs
    cfv
    cc0
    wceq
    @0
    cc0
    wceq
    @0
    abs00
    biimpa
    vy
    cv
    #
    @0
    absmul
    @0
    @1
    abstri
    cnnv.6
    isnvi
end
