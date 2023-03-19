include "cprb.mm"
include "wcel.mm"
include "cdm.mm"
include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "c0.mm"
include "domprobsiga.mm"
include "0elsiga.mm"
include "syl.mm"

theorem nuleldmp
  let cP: class P


  assert |- ( P e. Prob -> (/) e. dom P )

  proof
    cP
    cprb
    wcel
    cP
    cdm
    #
    csiga
    crn
    cuni
    wcel
    c0
    @0
    wcel
    cP
    domprobsiga
    @0
    0elsiga
    syl
end
