include "clmod.mm"
include "wcel.mm"
include "clinds.mm"
include "cfv.mm"
include "wss.mm"
include "w3a.mm"
include "cbs.mm"
include "cid.mm"
include "cres.mm"
include "clindf.mm"
include "wbr.mm"
include "wa.mm"
include "eqid.mm"
include "linds1.mm"
include "adantl.mm"
include "sstr2.mm"
include "syl5com.mm"
include "3impia.mm"
include "simp1.mm"
include "linds2.mm"
include "3ad2ant2.mm"
include "lindfres.mm"
include "syl2anc.mm"
include "wb.mm"
include "resabs1.mm"
include "breq1d.mm"
include "3ad2ant3.mm"
include "mpbid.mm"
include "islinds.mm"
include "3ad2ant1.mm"
include "mpbir2and.mm"

theorem lindsss
  let cF: class F
  let cG: class G
  let cW: class W


  assert |- ( ( W e. LMod /\ F e. ( LIndS ` W ) /\ G C_ F ) -> G e. ( LIndS ` W ) )

  proof
    cW
    clmod
    wcel
    #
    cF
    cW
    clinds
    cfv
    #
    wcel
    #
    cG
    cF
    wss
    #
    w3a
    #
    cG
    @1
    wcel
    #
    cG
    cW
    cbs
    cfv
    #
    wss
    #
    cid
    cG
    cres
    #
    cW
    clindf
    wbr
    #
    @0
    @2
    @3
    @7
    @0
    @2
    wa
    cF
    @6
    wss
    #
    @3
    @7
    @2
    @10
    @0
    @6
    cW
    cF
    @6
    eqid
    #
    linds1
    adantl
    cG
    cF
    @6
    sstr2
    syl5com
    3impia
    @4
    cid
    cF
    cres
    #
    cG
    cres
    #
    cW
    clindf
    wbr
    #
    @9
    @4
    @0
    @12
    cW
    clindf
    wbr
    #
    @14
    @0
    @2
    @3
    simp1
    @2
    @0
    @15
    @3
    cW
    cF
    linds2
    3ad2ant2
    @12
    cW
    cG
    lindfres
    syl2anc
    @3
    @0
    @14
    @9
    wb
    @2
    @3
    @13
    @8
    cW
    clindf
    cid
    cG
    cF
    resabs1
    breq1d
    3ad2ant3
    mpbid
    @0
    @2
    @5
    @7
    @9
    wa
    wb
    @3
    @6
    clmod
    cW
    cG
    @11
    islinds
    3ad2ant1
    mpbir2and
end
