include "cop.mm"
include "csn.mm"
include "csupp.mm"
include "co.mm"
include "cdm.mm"
include "suppssdm.mm"
include "dmsnopss.mm"
include "sstri.mm"

theorem snopsuppss
  let cX: class X
  let cY: class Y
  let cZ: class Z


  assert |- ( { <. X , Y >. } supp Z ) C_ { X }

  proof
    cX
    cY
    cop
    csn
    #
    cZ
    csupp
    co
    @0
    cdm
    cX
    csn
    @0
    cZ
    suppssdm
    cX
    cY
    dmsnopss
    sstri
end
