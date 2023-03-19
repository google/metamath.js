include "crrvec.mm"
include "cabl.mm"
include "ccmn.mm"
include "clmod.mm"
include "clvec.mm"
include "bj-rrvecssvec.mm"
include "bj-vecssmod.mm"
include "sstri.mm"
include "bj-modssabl.mm"
include "bj-ablsscmn.mm"

theorem bj-rrvecsscmn



  assert |- RRVec C_ CMnd

  proof
    crrvec
    cabl
    ccmn
    crrvec
    clmod
    cabl
    crrvec
    clvec
    clmod
    bj-rrvecssvec
    bj-vecssmod
    sstri
    bj-modssabl
    sstri
    bj-ablsscmn
    sstri
end
