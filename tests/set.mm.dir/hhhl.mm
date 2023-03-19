include "chlo.mm"
include "wcel.mm"
include "ccbn.mm"
include "ccphlo.mm"
include "cnv.mm"
include "cims.mm"
include "cfv.mm"
include "chil.mm"
include "cms.mm"
include "hhnv.mm"
include "eqid.mm"
include "hhcms.mm"
include "hhba.mm"
include "iscbn.mm"
include "mpbir2an.mm"
include "hhph.mm"
include "ishlo.mm"

theorem hhhl
  let cU: class U
  assume hhhl.1: |- U = <. <. +h , .h >. , normh >.


  assert |- U e. CHilOLD

  proof
    cU
    chlo
    wcel
    cU
    ccbn
    wcel
    #
    cU
    ccphlo
    wcel
    @0
    cU
    cnv
    wcel
    cU
    cims
    cfv
    #
    chil
    cms
    cfv
    wcel
    cU
    hhhl.1
    hhnv
    @1
    cU
    hhhl.1
    @1
    eqid
    #
    hhcms
    @1
    cU
    chil
    cU
    hhhl.1
    hhba
    @2
    iscbn
    mpbir2an
    cU
    hhhl.1
    hhph
    cU
    ishlo
    mpbir2an
end
