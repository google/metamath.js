include "cplig.mm"
include "wcel.mm"
include "cvv.mm"
include "csn.mm"
include "c0.mm"
include "nsnlplig.mm"
include "wn.mm"
include "wceq.mm"
include "elirr.mm"
include "snprc.mm"
include "mpbi.mm"
include "eqcomi.mm"
include "eleq1i.mm"
include "sylnibr.mm"

theorem n0lplig
  let cG: class G


  assert |- ( G e. Plig -> -. (/) e. G )

  proof
    cG
    cplig
    wcel
    cvv
    csn
    #
    cG
    wcel
    c0
    cG
    wcel
    cvv
    cG
    nsnlplig
    c0
    @0
    cG
    @0
    c0
    cvv
    cvv
    wcel
    wn
    @0
    c0
    wceq
    cvv
    elirr
    cvv
    snprc
    mpbi
    eqcomi
    eleq1i
    sylnibr
end
