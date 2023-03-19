include "wnfc.mm"
include "cv.mm"
include "wcel.mm"
include "wal.mm"
include "sp.mm"
include "nfcr.mm"
include "nf5rd.mm"
include "impbid2.mm"
include "abbi1dv.mm"

theorem abidnf
  let vx: setvar x
  let vz: setvar z
  let cA: class A

  disjoint x z
  disjoint A z
  assert |- ( F/_ x A -> { z | A. x z e. A } = A )

  proof
    vx
    cA
    wnfc
    #
    vz
    cv
    cA
    wcel
    #
    vx
    wal
    #
    vz
    cA
    @0
    @2
    @1
    @1
    vx
    sp
    @0
    @1
    vx
    vx
    vz
    cA
    nfcr
    nf5rd
    impbid2
    abbi1dv
end
