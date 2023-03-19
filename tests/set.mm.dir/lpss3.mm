include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "clp.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "ccl.mm"
include "simp1.mm"
include "simp2.mm"
include "ssdifssd.mm"
include "simp3.mm"
include "ssdifd.mm"
include "clsss.mm"
include "syl3anc.mm"
include "sseld.mm"
include "wb.mm"
include "sstrd.mm"
include "islp.mm"
include "syl2anc.mm"
include "3imtr4d.mm"
include "ssrdv.mm"

theorem lpss3
  let cS: class S
  let cT: class T
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  assume lpfval.1: |- X = U. J


  assert |- ( ( J e. Top /\ S C_ X /\ T C_ S ) -> ( ( limPt ` J ) ` T ) C_ ( ( limPt ` J ) ` S ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    cT
    cS
    wss
    #
    w3a
    #
    vx
    cT
    cJ
    clp
    cfv
    #
    cfv
    #
    cS
    @4
    cfv
    #
    @3
    vx
    cv
    #
    cT
    @7
    csn
    #
    cdif
    #
    cJ
    ccl
    cfv
    #
    cfv
    #
    wcel
    #
    @7
    cS
    @8
    cdif
    #
    @10
    cfv
    #
    wcel
    #
    @7
    @5
    wcel
    #
    @7
    @6
    wcel
    #
    @3
    @11
    @14
    @7
    @3
    @0
    @13
    cX
    wss
    @9
    @13
    wss
    @11
    @14
    wss
    @0
    @1
    @2
    simp1
    #
    @3
    cS
    cX
    @8
    @0
    @1
    @2
    simp2
    #
    ssdifssd
    @3
    cT
    cS
    @8
    @0
    @1
    @2
    simp3
    #
    ssdifd
    @13
    @9
    cJ
    cX
    lpfval.1
    clsss
    syl3anc
    sseld
    @3
    @0
    cT
    cX
    wss
    @16
    @12
    wb
    @18
    @3
    cT
    cS
    cX
    @20
    @19
    sstrd
    @7
    cT
    cJ
    cX
    lpfval.1
    islp
    syl2anc
    @3
    @0
    @1
    @17
    @15
    wb
    @18
    @19
    @7
    cS
    cJ
    cX
    lpfval.1
    islp
    syl2anc
    3imtr4d
    ssrdv
end
