include "chlo.mm"
include "wcel.mm"
include "ccbn.mm"
include "ccphlo.mm"
include "hhssbn.mm"
include "chshii.mm"
include "hhssph.mm"
include "ishlo.mm"
include "mpbir2an.mm"

theorem hhsshl
  let cH: class H
  let cW: class W
  assume hhssbn.1: |- W = <. <. ( +h |` ( H X. H ) ) , ( .h |` ( CC X. H ) ) >. , ( normh |` H ) >.
  assume hhssbn.2: |- H e. CH


  assert |- W e. CHilOLD

  proof
    cW
    chlo
    wcel
    cW
    ccbn
    wcel
    cW
    ccphlo
    wcel
    cH
    cW
    hhssbn.1
    hhssbn.2
    hhssbn
    cH
    cW
    hhssbn.1
    cH
    hhssbn.2
    chshii
    hhssph
    cW
    ishlo
    mpbir2an
end
