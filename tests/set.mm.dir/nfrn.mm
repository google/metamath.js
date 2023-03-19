include "crn.mm"
include "ccnv.mm"
include "cdm.mm"
include "df-rn.mm"
include "nfcnv.mm"
include "nfdm.mm"
include "nfcxfr.mm"

theorem nfrn
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z
  assume nfrn.1: |- F/_ x A


  assert |- F/_ x ran A

  proof
    vx
    cA
    crn
    cA
    ccnv
    #
    cdm
    cA
    df-rn
    vx
    @0
    vx
    cA
    nfrn.1
    nfcnv
    nfdm
    nfcxfr
end
