include "cnv.mm"
include "wcel.mm"
include "cme.mm"
include "cfv.mm"
include "hhssnv.mm"
include "hhssba.mm"
include "imsmet.mm"
include "ax-mp.mm"

theorem hhssmet
  let cD: class D
  let cH: class H
  let cW: class W
  assume hhssims2.1: |- W = <. <. ( +h |` ( H X. H ) ) , ( .h |` ( CC X. H ) ) >. , ( normh |` H ) >.
  assume hhssims2.3: |- D = ( IndMet ` W )
  assume hhssims2.2: |- H e. SH


  assert |- D e. ( Met ` H )

  proof
    cW
    cnv
    wcel
    cD
    cH
    cme
    cfv
    wcel
    cH
    cW
    hhssims2.1
    hhssims2.2
    hhssnv
    cD
    cW
    cH
    cH
    cW
    hhssims2.1
    hhssims2.2
    hhssba
    hhssims2.3
    imsmet
    ax-mp
end
