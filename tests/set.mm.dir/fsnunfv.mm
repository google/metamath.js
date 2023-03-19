include "wcel.mm"
include "cdm.mm"
include "wn.mm"
include "w3a.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cres.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cin.mm"
include "dmres.mm"
include "incom.mm"
include "eqtri.mm"
include "disjsn.mm"
include "biimpri.mm"
include "syl5eq.mm"
include "3ad2ant3.mm"
include "wrel.mm"
include "wb.mm"
include "relres.mm"
include "reldm0.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "wfn.mm"
include "fnsng.mm"
include "3adant3.mm"
include "fnresdm.mm"
include "syl.mm"
include "uneq12d.mm"
include "resundir.mm"
include "uncom.mm"
include "un0.mm"
include "eqtr2i.mm"
include "3eqtr4g.mm"
include "fveq1d.mm"
include "snidg.mm"
include "3ad2ant1.mm"
include "fvres.mm"
include "fvsng.mm"
include "3eqtr3d.mm"

theorem fsnunfv
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y


  assert |- ( ( X e. V /\ Y e. W /\ -. X e. dom F ) -> ( ( F u. { <. X , Y >. } ) ` X ) = Y )

  proof
    cX
    cV
    wcel
    #
    cY
    cW
    wcel
    #
    cX
    cF
    cdm
    #
    wcel
    wn
    #
    w3a
    #
    cX
    cF
    cX
    cY
    cop
    csn
    #
    cun
    #
    cX
    csn
    #
    cres
    #
    cfv
    #
    cX
    @5
    cfv
    #
    cX
    @6
    cfv
    #
    cY
    @4
    cX
    @8
    @5
    @4
    cF
    @7
    cres
    #
    @5
    @7
    cres
    #
    cun
    c0
    @5
    cun
    #
    @8
    @5
    @4
    @12
    c0
    @13
    @5
    @4
    @12
    cdm
    #
    c0
    wceq
    #
    @12
    c0
    wceq
    #
    @3
    @0
    @16
    @1
    @3
    @15
    @2
    @7
    cin
    #
    c0
    @15
    @7
    @2
    cin
    @18
    cF
    @7
    dmres
    @7
    @2
    incom
    eqtri
    @18
    c0
    wceq
    @3
    @2
    cX
    disjsn
    biimpri
    syl5eq
    3ad2ant3
    @12
    wrel
    @17
    @16
    wb
    cF
    @7
    relres
    @12
    reldm0
    ax-mp
    sylibr
    @4
    @5
    @7
    wfn
    #
    @13
    @5
    wceq
    @0
    @1
    @19
    @3
    cX
    cY
    cV
    cW
    fnsng
    3adant3
    @7
    @5
    fnresdm
    syl
    uneq12d
    cF
    @5
    @7
    resundir
    @14
    @5
    c0
    cun
    @5
    c0
    @5
    uncom
    @5
    un0
    eqtr2i
    3eqtr4g
    fveq1d
    @4
    cX
    @7
    wcel
    #
    @9
    @11
    wceq
    @0
    @1
    @20
    @3
    cX
    cV
    snidg
    3ad2ant1
    cX
    @7
    @6
    fvres
    syl
    @0
    @1
    @10
    cY
    wceq
    @3
    cX
    cY
    cV
    cW
    fvsng
    3adant3
    3eqtr3d
end
