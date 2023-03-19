include "cnv.mm"
include "wcel.mm"
include "cxp.mm"
include "cmv.mm"
include "cres.mm"
include "wf.mm"
include "hhssnv.mm"
include "hhssba.mm"
include "hhssvs.mm"
include "nvmf.mm"
include "ax-mp.mm"

theorem hhssvsf
  let cH: class H
  let cW: class W
  assume hhsssh2.1: |- W = <. <. ( +h |` ( H X. H ) ) , ( .h |` ( CC X. H ) ) >. , ( normh |` H ) >.
  assume hhssba.2: |- H e. SH


  assert |- ( -h |` ( H X. H ) ) : ( H X. H ) --> H

  proof
    cW
    cnv
    wcel
    cH
    cH
    cxp
    #
    cH
    cmv
    @0
    cres
    #
    wf
    cH
    cW
    hhsssh2.1
    hhssba.2
    hhssnv
    cW
    @1
    cH
    cH
    cW
    hhsssh2.1
    hhssba.2
    hhssba
    cH
    cW
    hhsssh2.1
    hhssba.2
    hhssvs
    nvmf
    ax-mp
end
