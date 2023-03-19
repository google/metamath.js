include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "cv.mm"
include "ccnv.mm"
include "cfv.mm"
include "cdm.mm"
include "wf1o.mm"
include "wceq.mm"
include "diaf11N.mm"
include "f1ocnvfv2.mm"
include "sylan.mm"
include "cbs.mm"
include "cple.mm"
include "wbr.mm"
include "diacnvclN.mm"
include "wb.mm"
include "eqid.mm"
include "diaeldm.mm"
include "adantr.mm"
include "mpbid.mm"
include "dialss.mm"
include "syldan.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "ssrdv.mm"

theorem diasslssN
  let cS: class S
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let vx: setvar x
  assume diasslss.h: |- H = ( LHyp ` K )
  assume diasslss.u: |- U = ( ( DVecA ` K ) ` W )
  assume diasslss.i: |- I = ( ( DIsoA ` K ) ` W )
  assume diasslss.s: |- S = ( LSubSp ` U )


  assert |- ( ( K e. HL /\ W e. H ) -> ran I C_ S )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    vx
    cI
    crn
    #
    cS
    @0
    vx
    cv
    #
    @1
    wcel
    #
    @2
    cS
    wcel
    @0
    @3
    wa
    #
    @2
    cI
    ccnv
    cfv
    #
    cI
    cfv
    #
    @2
    cS
    @0
    cI
    cdm
    #
    @1
    cI
    wf1o
    @3
    @6
    @2
    wceq
    cH
    cI
    cK
    cW
    diasslss.h
    diasslss.i
    diaf11N
    @7
    @1
    @2
    cI
    f1ocnvfv2
    sylan
    @0
    @3
    @5
    cK
    cbs
    cfv
    #
    wcel
    @5
    cW
    cK
    cple
    cfv
    #
    wbr
    wa
    #
    @6
    cS
    wcel
    @4
    @5
    @7
    wcel
    #
    @10
    cH
    cI
    cK
    cW
    @2
    diasslss.h
    diasslss.i
    diacnvclN
    @0
    @11
    @10
    wb
    @3
    @8
    cH
    cI
    cK
    @9
    chlt
    cW
    @5
    @8
    eqid
    #
    @9
    eqid
    #
    diasslss.h
    diasslss.i
    diaeldm
    adantr
    mpbid
    @8
    cS
    cU
    cH
    cI
    cK
    @9
    cW
    @5
    @12
    @13
    diasslss.h
    diasslss.u
    diasslss.i
    diasslss.s
    dialss
    syldan
    eqeltrrd
    ex
    ssrdv
end
