include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cv.mm"
include "wex.mm"
include "wn.mm"
include "wa.mm"
include "cle.mm"
include "c0.mm"
include "wceq.mm"
include "wal.mm"
include "wi.mm"
include "alnex.mm"
include "eq0.mm"
include "biimpri.mm"
include "a1d.mm"
include "sylbir.mm"
include "impcom.mm"
include "wb.mm"
include "hashle00.mm"
include "adantr.mm"
include "mpbird.mm"
include "cxr.mm"
include "hashxrcl.mm"
include "0xr.mm"
include "xrlenlt.mm"
include "sylancl.mm"
include "bicomd.mm"
include "ex.mm"
include "con4d.mm"
include "imp.mm"

theorem hashgt0elex
  let vx: setvar x
  let cV: class V
  let cW: class W

  disjoint V x
  assert |- ( ( V e. W /\ 0 < ( # ` V ) ) -> E. x x e. V )

  proof
    cV
    cW
    wcel
    #
    cc0
    cV
    chash
    cfv
    #
    clt
    wbr
    #
    vx
    cv
    cV
    wcel
    #
    vx
    wex
    #
    @0
    @4
    @2
    @0
    @4
    wn
    #
    @2
    wn
    #
    @0
    @5
    wa
    #
    @6
    @1
    cc0
    cle
    wbr
    #
    @7
    @8
    cV
    c0
    wceq
    #
    @5
    @0
    @9
    @5
    @3
    wn
    vx
    wal
    #
    @0
    @9
    wi
    @3
    vx
    alnex
    @10
    @9
    @0
    @9
    @10
    vx
    cV
    eq0
    biimpri
    a1d
    sylbir
    impcom
    @0
    @8
    @9
    wb
    @5
    cV
    cW
    hashle00
    adantr
    mpbird
    @0
    @6
    @8
    wb
    @5
    @0
    @8
    @6
    @0
    @1
    cxr
    wcel
    cc0
    cxr
    wcel
    @8
    @6
    wb
    cV
    cW
    hashxrcl
    0xr
    @1
    cc0
    xrlenlt
    sylancl
    bicomd
    adantr
    mpbird
    ex
    con4d
    imp
end
