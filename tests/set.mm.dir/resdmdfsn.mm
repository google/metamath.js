include "wrel.mm"
include "cdm.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cvv.mm"
include "cin.mm"
include "indif1.mm"
include "incom.mm"
include "inv1.mm"
include "eqtri.mm"
include "difeq1i.mm"
include "reseq2i.mm"
include "resindm.mm"
include "syl5reqr.mm"

theorem resdmdfsn
  let cR: class R
  let cX: class X


  assert |- ( Rel R -> ( R |` ( _V \ { X } ) ) = ( R |` ( dom R \ { X } ) ) )

  proof
    cR
    wrel
    cR
    cR
    cdm
    #
    cX
    csn
    #
    cdif
    #
    cres
    cR
    cvv
    @1
    cdif
    #
    @0
    cin
    #
    cres
    cR
    @3
    cres
    @4
    @2
    cR
    @4
    cvv
    @0
    cin
    #
    @1
    cdif
    @2
    cvv
    @0
    @1
    indif1
    @5
    @0
    @1
    @5
    @0
    cvv
    cin
    @0
    cvv
    @0
    incom
    @0
    inv1
    eqtri
    difeq1i
    eqtri
    reseq2i
    cR
    @3
    resindm
    syl5reqr
end
