include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "wceq.mm"
include "simp3.mm"
include "cxr.mm"
include "wa.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "measvxrge0.mm"
include "elxrge0.mm"
include "sylib.mm"
include "3adant3.mm"
include "simprd.mm"
include "wb.mm"
include "simpld.mm"
include "0xr.mm"
include "xrletri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"

theorem measle0
  let cA: class A
  let cS: class S
  let cM: class M


  assert |- ( ( M e. ( measures ` S ) /\ A e. S /\ ( M ` A ) <_ 0 ) -> ( M ` A ) = 0 )

  proof
    cM
    cS
    cmeas
    cfv
    wcel
    #
    cA
    cS
    wcel
    #
    cA
    cM
    cfv
    #
    cc0
    cle
    wbr
    #
    w3a
    #
    @2
    cc0
    wceq
    #
    @3
    cc0
    @2
    cle
    wbr
    #
    @0
    @1
    @3
    simp3
    @4
    @2
    cxr
    wcel
    #
    @6
    @0
    @1
    @7
    @6
    wa
    #
    @3
    @0
    @1
    wa
    @2
    cc0
    cpnf
    cicc
    co
    wcel
    @8
    cA
    cS
    cM
    measvxrge0
    @2
    elxrge0
    sylib
    3adant3
    #
    simprd
    @4
    @7
    cc0
    cxr
    wcel
    @5
    @3
    @6
    wa
    wb
    @4
    @7
    @6
    @9
    simpld
    0xr
    @2
    cc0
    xrletri3
    sylancl
    mpbir2and
end
