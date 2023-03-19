include "cdmn.mm"
include "wcel.mm"
include "cprrng.mm"
include "ccm2.mm"
include "wa.mm"
include "ccring.mm"
include "isdmn.mm"
include "crngo.mm"
include "wb.mm"
include "prrngorngo.mm"
include "iscrngo.mm"
include "baibr.mm"
include "syl.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem isdmn2
  let cR: class R


  assert |- ( R e. Dmn <-> ( R e. PrRing /\ R e. CRingOps ) )

  proof
    cR
    cdmn
    wcel
    cR
    cprrng
    wcel
    #
    cR
    ccm2
    wcel
    #
    wa
    @0
    cR
    ccring
    wcel
    #
    wa
    cR
    isdmn
    @0
    @1
    @2
    @0
    cR
    crngo
    wcel
    #
    @1
    @2
    wb
    cR
    prrngorngo
    @2
    @3
    @1
    cR
    iscrngo
    baibr
    syl
    pm5.32i
    bitri
end
