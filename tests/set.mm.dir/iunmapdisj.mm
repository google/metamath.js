include "cv.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wrmo.mm"
include "wa.mm"
include "wmo.mm"
include "cdm.mm"
include "wceq.mm"
include "moeq.mm"
include "wf.mm"
include "elmapi.mm"
include "fdm.mm"
include "eqcomd.mm"
include "syl.mm"
include "moimi.mm"
include "ax-mp.mm"
include "moani.mm"
include "df-rmo.mm"
include "mpbir.mm"

theorem iunmapdisj
  let cA: class A
  let cB: class B
  let cC: class C
  let vn: setvar n

  disjoint B n
  assert |- E* n e. C B e. ( A ^m n )

  proof
    cB
    cA
    vn
    cv
    #
    cmap
    co
    wcel
    #
    vn
    cC
    wrmo
    @0
    cC
    wcel
    #
    @1
    wa
    vn
    wmo
    @1
    @2
    vn
    @0
    cB
    cdm
    #
    wceq
    #
    vn
    wmo
    @1
    vn
    wmo
    vn
    @3
    moeq
    @1
    @4
    vn
    @1
    @0
    cA
    cB
    wf
    #
    @4
    cB
    cA
    @0
    elmapi
    @5
    @3
    @0
    @0
    cA
    cB
    fdm
    eqcomd
    syl
    moimi
    ax-mp
    moani
    @1
    vn
    cC
    df-rmo
    mpbir
end
