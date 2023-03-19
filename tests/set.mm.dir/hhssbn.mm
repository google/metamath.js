include "ccbn.mm"
include "wcel.mm"
include "cnv.mm"
include "cims.mm"
include "cfv.mm"
include "cms.mm"
include "chshii.mm"
include "hhssnv.mm"
include "eqid.mm"
include "hhsscms.mm"
include "hhssba.mm"
include "iscbn.mm"
include "mpbir2an.mm"

theorem hhssbn
  let cH: class H
  let cW: class W
  assume hhssbn.1: |- W = <. <. ( +h |` ( H X. H ) ) , ( .h |` ( CC X. H ) ) >. , ( normh |` H ) >.
  assume hhssbn.2: |- H e. CH


  assert |- W e. CBan

  proof
    cW
    ccbn
    wcel
    cW
    cnv
    wcel
    cW
    cims
    cfv
    #
    cH
    cms
    cfv
    wcel
    cH
    cW
    hhssbn.1
    cH
    hhssbn.2
    chshii
    #
    hhssnv
    @0
    cH
    cW
    hhssbn.1
    @0
    eqid
    #
    hhssbn.2
    hhsscms
    @0
    cW
    cH
    cH
    cW
    hhssbn.1
    @1
    hhssba
    @2
    iscbn
    mpbir2an
end
