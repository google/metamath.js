include "cdir.mm"
include "wcel.mm"
include "wrel.mm"
include "cid.mm"
include "cuni.mm"
include "cres.mm"
include "wss.mm"
include "ccom.mm"
include "cxp.mm"
include "ccnv.mm"
include "wa.mm"
include "eqid.mm"
include "isdir.mm"
include "ibi.mm"
include "simplld.mm"

theorem reldir
  let cR: class R


  assert |- ( R e. DirRel -> Rel R )

  proof
    cR
    cdir
    wcel
    #
    cR
    wrel
    #
    cid
    cR
    cuni
    cuni
    #
    cres
    cR
    wss
    #
    cR
    cR
    ccom
    cR
    wss
    @2
    @2
    cxp
    cR
    ccnv
    cR
    ccom
    wss
    wa
    #
    @0
    @1
    @3
    wa
    @4
    wa
    @2
    cR
    cdir
    @2
    eqid
    isdir
    ibi
    simplld
end
