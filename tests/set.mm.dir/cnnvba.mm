include "caddc.mm"
include "crn.mm"
include "cpv.mm"
include "cfv.mm"
include "cc.mm"
include "cba.mm"
include "cnnvg.mm"
include "rneqi.mm"
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
include "eqid.mm"
include "bafval.mm"
include "3eqtr4i.mm"

theorem cnnvba
  let cU: class U
  assume cnnvba.6: |- U = <. <. + , x. >. , abs >.


  assert |- CC = ( BaseSet ` U )

  proof
    caddc
    crn
    cU
    cpv
    cfv
    #
    crn
    cc
    cU
    cba
    cfv
    #
    caddc
    @0
    cU
    cnnvba.6
    cnnvg
    rneqi
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
    cU
    @0
    @1
    @1
    eqid
    @0
    eqid
    bafval
    3eqtr4i
end
