include "cdm.mm"
include "wcel.mm"
include "csn.mm"
include "cres.mm"
include "eldmressnsn.mm"
include "cin.mm"
include "elinel2.mm"
include "dmres.mm"
include "eleq2s.mm"
include "impbii.mm"

theorem eldmeldmressn
  let cF: class F
  let cX: class X


  assert |- ( X e. dom F <-> X e. dom ( F |` { X } ) )

  proof
    cX
    cF
    cdm
    #
    wcel
    #
    cX
    cF
    cX
    csn
    #
    cres
    cdm
    #
    wcel
    cX
    cF
    eldmressnsn
    @1
    cX
    @2
    @0
    cin
    @3
    cX
    @2
    @0
    elinel2
    cF
    @2
    dmres
    eleq2s
    impbii
end
