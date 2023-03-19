include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "cdif.mm"
include "wi.mm"
include "wal.mm"
include "wn.mm"
include "wb.mm"
include "ssel.mm"
include "pm5.1.mm"
include "syl2an.mm"
include "con2b.mm"
include "a1i.mm"
include "anbi12d.mm"
include "jcab.mm"
include "3bitr4g.mm"
include "eldif.mm"
include "imbi2i.mm"
include "albidv.mm"
include "dfss2.mm"

theorem ssconb
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( A C_ C /\ B C_ C ) -> ( A C_ ( C \ B ) <-> B C_ ( C \ A ) ) )

  proof
    cA
    cC
    wss
    #
    cB
    cC
    wss
    #
    wa
    #
    vx
    cv
    #
    cA
    wcel
    #
    @3
    cC
    cB
    cdif
    #
    wcel
    #
    wi
    #
    vx
    wal
    @3
    cB
    wcel
    #
    @3
    cC
    cA
    cdif
    #
    wcel
    #
    wi
    #
    vx
    wal
    cA
    @5
    wss
    cB
    @9
    wss
    @2
    @7
    @11
    vx
    @2
    @4
    @3
    cC
    wcel
    #
    @8
    wn
    #
    wa
    #
    wi
    #
    @8
    @12
    @4
    wn
    #
    wa
    #
    wi
    #
    @7
    @11
    @2
    @4
    @12
    wi
    #
    @4
    @13
    wi
    #
    wa
    @8
    @12
    wi
    #
    @8
    @16
    wi
    #
    wa
    @15
    @18
    @2
    @19
    @21
    @20
    @22
    @0
    @19
    @21
    @19
    @21
    wb
    @1
    cA
    cC
    @3
    ssel
    cB
    cC
    @3
    ssel
    @19
    @21
    pm5.1
    syl2an
    @20
    @22
    wb
    @2
    @4
    @8
    con2b
    a1i
    anbi12d
    @4
    @12
    @13
    jcab
    @8
    @12
    @16
    jcab
    3bitr4g
    @6
    @14
    @4
    @3
    cC
    cB
    eldif
    imbi2i
    @10
    @17
    @8
    @3
    cC
    cA
    eldif
    imbi2i
    3bitr4g
    albidv
    vx
    cA
    @5
    dfss2
    vx
    cB
    @9
    dfss2
    3bitr4g
end
