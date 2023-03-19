include "wcel.mm"
include "wrel.mm"
include "cc0.mm"
include "crelexp.mm"
include "co.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "cuni.mm"
include "relexp0g.mm"
include "relfld.mm"
include "reseq2d.mm"
include "eqcomd.mm"
include "sylan9eq.mm"

theorem relexp0
  let cR: class R
  let cV: class V


  assert |- ( ( R e. V /\ Rel R ) -> ( R ^r 0 ) = ( _I |` U. U. R ) )

  proof
    cR
    cV
    wcel
    cR
    wrel
    #
    cR
    cc0
    crelexp
    co
    cid
    cR
    cdm
    cR
    crn
    cun
    #
    cres
    #
    cid
    cR
    cuni
    cuni
    #
    cres
    #
    cR
    cV
    relexp0g
    @0
    @4
    @2
    @0
    @3
    @1
    cid
    cR
    relfld
    reseq2d
    eqcomd
    sylan9eq
end
