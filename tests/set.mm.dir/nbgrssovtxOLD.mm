include "wcel.mm"
include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "wa.mm"
include "wne.mm"
include "nbgrisvtxOLD.mm"
include "wceq.mm"
include "wn.mm"
include "wnel.mm"
include "nbgrnself2OLD.mm"
include "adantr.mm"
include "df-nel.mm"
include "wb.mm"
include "neleq1.mm"
include "adantl.mm"
include "syl5bbr.mm"
include "mpbird.mm"
include "ex.mm"
include "con2d.mm"
include "imp.mm"
include "neqned.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "ssrdv.mm"

theorem nbgrssovtxOLD
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vv: setvar v
  assume nbgrssovtxOLD.v: |- V = ( Vtx ` G )


  assert |- ( G e. W -> ( G NeighbVtx N ) C_ ( V \ { N } ) )

  proof
    cG
    cW
    wcel
    #
    vv
    cG
    cN
    cnbgr
    co
    #
    cV
    cN
    csn
    cdif
    #
    @0
    vv
    cv
    #
    @1
    wcel
    #
    @3
    @2
    wcel
    #
    @0
    @4
    wa
    #
    @3
    cV
    wcel
    @3
    cN
    wne
    @5
    cG
    cN
    @3
    cV
    cW
    nbgrssovtxOLD.v
    nbgrisvtxOLD
    @6
    @3
    cN
    @0
    @4
    @3
    cN
    wceq
    #
    wn
    @0
    @7
    @4
    @0
    @7
    @4
    wn
    #
    @0
    @7
    wa
    #
    @8
    cN
    @1
    wnel
    #
    @0
    @10
    @7
    cG
    cN
    cW
    nbgrnself2OLD
    adantr
    @8
    @3
    @1
    wnel
    #
    @9
    @10
    @3
    @1
    df-nel
    @7
    @11
    @10
    wb
    @0
    @3
    cN
    @1
    neleq1
    adantl
    syl5bbr
    mpbird
    ex
    con2d
    imp
    neqned
    @3
    cV
    cN
    eldifsn
    sylanbrc
    ex
    ssrdv
end
