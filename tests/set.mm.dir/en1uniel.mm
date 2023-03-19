include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "cuni.mm"
include "csn.mm"
include "cvv.mm"
include "wcel.mm"
include "relen.mm"
include "brrelexi.mm"
include "uniexg.mm"
include "snidg.mm"
include "3syl.mm"
include "wceq.mm"
include "en1b.mm"
include "biimpi.mm"
include "eleqtrrd.mm"

theorem en1uniel
  let cS: class S


  assert |- ( S ~~ 1o -> U. S e. S )

  proof
    cS
    c1o
    cen
    wbr
    #
    cS
    cuni
    #
    @1
    csn
    #
    cS
    @0
    cS
    cvv
    wcel
    @1
    cvv
    wcel
    @1
    @2
    wcel
    cS
    c1o
    cen
    relen
    brrelexi
    cS
    cvv
    uniexg
    @1
    cvv
    snidg
    3syl
    @0
    cS
    @2
    wceq
    cS
    en1b
    biimpi
    eleqtrrd
end
