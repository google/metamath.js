include "wcel.mm"
include "csn.mm"
include "bj-ctag.mm"
include "cxp.mm"
include "bj-cproj.mm"
include "wceq.mm"
include "c0.mm"
include "cif.mm"
include "wi.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "cima.mm"
include "cab.mm"
include "elsng.mm"
include "bj-xpima2sn.mm"
include "syl6bir.mm"
include "imp.mm"
include "eleq2d.mm"
include "abbidv.mm"
include "df-bj-proj.mm"
include "bj-taginv.mm"
include "3eqtr4g.mm"
include "ex.mm"
include "noel.mm"
include "abeq2i.mm"
include "wnel.mm"
include "elsni.mm"
include "con3i.mm"
include "df-nel.mm"
include "sylibr.mm"
include "bj-xpima1sn.mm"
include "syl.mm"
include "syl5bb.mm"
include "mtbiri.mm"
include "eq0rdv.mm"
include "ifval.mm"
include "sylanblrc.mm"
include "wb.mm"
include "eqcom.mm"
include "ifbi.mm"
include "ax-mp.mm"
include "syl6eq.mm"

theorem bj-projval
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> ( A Proj ( { B } X. tag C ) ) = if ( B = A , C , (/) ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cB
    csn
    #
    cC
    bj-ctag
    #
    cxp
    #
    bj-cproj
    #
    cA
    cB
    wceq
    #
    cC
    c0
    cif
    #
    cB
    cA
    wceq
    #
    cC
    c0
    cif
    #
    @0
    @5
    @4
    cC
    wceq
    #
    wi
    @5
    wn
    #
    @4
    c0
    wceq
    wi
    @4
    @6
    wceq
    @0
    @5
    @9
    @0
    @5
    wa
    #
    vx
    cv
    #
    csn
    #
    @3
    cA
    csn
    cima
    #
    wcel
    #
    vx
    cab
    @13
    @2
    wcel
    #
    vx
    cab
    @4
    cC
    @11
    @15
    @16
    vx
    @11
    @14
    @2
    @13
    @0
    @5
    @14
    @2
    wceq
    #
    @0
    @5
    cA
    @1
    wcel
    #
    @17
    cA
    cB
    cV
    elsng
    @1
    @2
    cA
    bj-xpima2sn
    syl6bir
    imp
    eleq2d
    abbidv
    vx
    cA
    @3
    df-bj-proj
    #
    vx
    cC
    bj-taginv
    3eqtr4g
    ex
    @10
    vx
    @4
    @10
    @12
    @4
    wcel
    #
    @13
    c0
    wcel
    #
    @13
    noel
    @20
    @15
    @10
    @21
    @15
    vx
    @4
    @19
    abeq2i
    @10
    @14
    c0
    @13
    @10
    cA
    @1
    wnel
    #
    @14
    c0
    wceq
    @10
    @18
    wn
    @22
    @18
    @5
    cA
    cB
    elsni
    con3i
    cA
    @1
    df-nel
    sylibr
    @1
    @2
    cA
    bj-xpima1sn
    syl
    eleq2d
    syl5bb
    mtbiri
    eq0rdv
    @5
    @4
    cC
    c0
    ifval
    sylanblrc
    @5
    @7
    wb
    @6
    @8
    wceq
    cA
    cB
    eqcom
    @5
    @7
    cC
    c0
    ifbi
    ax-mp
    syl6eq
end
