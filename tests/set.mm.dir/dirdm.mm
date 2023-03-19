include "cdir.mm"
include "wcel.mm"
include "cdm.mm"
include "cuni.mm"
include "wss.mm"
include "crn.mm"
include "cun.mm"
include "ssun1.mm"
include "dmrnssfld.mm"
include "sstri.mm"
include "a1i.mm"
include "cid.mm"
include "cres.mm"
include "dmresi.mm"
include "wrel.mm"
include "wa.mm"
include "ccom.mm"
include "cxp.mm"
include "ccnv.mm"
include "eqid.mm"
include "isdir.mm"
include "ibi.mm"
include "simpld.mm"
include "simprd.mm"
include "dmss.mm"
include "syl.mm"
include "syl5eqssr.mm"
include "eqssd.mm"

theorem dirdm
  let cR: class R


  assert |- ( R e. DirRel -> dom R = U. U. R )

  proof
    cR
    cdir
    wcel
    #
    cR
    cdm
    #
    cR
    cuni
    cuni
    #
    @1
    @2
    wss
    @0
    @1
    @1
    cR
    crn
    #
    cun
    @2
    @1
    @3
    ssun1
    cR
    dmrnssfld
    sstri
    a1i
    @0
    @2
    cid
    @2
    cres
    #
    cdm
    #
    @1
    @2
    dmresi
    @0
    @4
    cR
    wss
    #
    @5
    @1
    wss
    @0
    cR
    wrel
    #
    @6
    @0
    @7
    @6
    wa
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
    @8
    @9
    wa
    @2
    cR
    cdir
    @2
    eqid
    isdir
    ibi
    simpld
    simprd
    @4
    cR
    dmss
    syl
    syl5eqssr
    eqssd
end
