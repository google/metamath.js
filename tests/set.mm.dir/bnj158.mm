include "cv.mm"
include "wcel.mm"
include "com.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "csuc.mm"
include "wceq.mm"
include "wrex.mm"
include "csn.mm"
include "cdif.mm"
include "eleq2i.mm"
include "eldifsn.mm"
include "bitri.mm"
include "nnsuc.mm"
include "sylbi.mm"

theorem bnj158
  let cD: class D
  let vm: setvar m
  let vp: setvar p
  assume bnj158.1: |- D = ( _om \ { (/) } )

  disjoint m p
  assert |- ( m e. D -> E. p e. _om m = suc p )

  proof
    vm
    cv
    #
    cD
    wcel
    #
    @0
    com
    wcel
    @0
    c0
    wne
    wa
    #
    @0
    vp
    cv
    csuc
    wceq
    vp
    com
    wrex
    @1
    @0
    com
    c0
    csn
    cdif
    #
    wcel
    @2
    cD
    @3
    @0
    bnj158.1
    eleq2i
    @0
    com
    c0
    eldifsn
    bitri
    vp
    @0
    nnsuc
    sylbi
end
