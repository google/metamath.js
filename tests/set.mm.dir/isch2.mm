include "cch.mm"
include "wcel.mm"
include "csh.mm"
include "chli.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wf.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "isch.mm"
include "alcom.mm"
include "wex.mm"
include "19.23v.mm"
include "vex.mm"
include "elima2.mm"
include "imbi1i.mm"
include "bitr4i.mm"
include "albii.mm"
include "dfss2.mm"
include "bitri.mm"
include "cvv.mm"
include "wb.mm"
include "nnex.mm"
include "elmapg.mm"
include "mpan2.mm"
include "anbi1d.mm"
include "imbi1d.mm"
include "2albidv.mm"
include "syl5bbr.mm"
include "pm5.32i.mm"

theorem isch2
  let vx: setvar x
  let vf: setvar f
  let cH: class H

  disjoint f x
  disjoint H x
  disjoint H f
  assert |- ( H e. CH <-> ( H e. SH /\ A. f A. x ( ( f : NN --> H /\ f ~~>v x ) -> x e. H ) ) )

  proof
    cH
    cch
    wcel
    cH
    csh
    wcel
    #
    chli
    cH
    cn
    cmap
    co
    #
    cima
    #
    cH
    wss
    #
    wa
    @0
    cn
    cH
    vf
    cv
    #
    wf
    #
    @4
    vx
    cv
    #
    chli
    wbr
    #
    wa
    #
    @6
    cH
    wcel
    #
    wi
    #
    vx
    wal
    vf
    wal
    #
    wa
    cH
    isch
    @0
    @3
    @11
    @3
    @4
    @1
    wcel
    #
    @7
    wa
    #
    @9
    wi
    #
    vx
    wal
    vf
    wal
    #
    @0
    @11
    @15
    @14
    vf
    wal
    #
    vx
    wal
    #
    @3
    @14
    vf
    vx
    alcom
    @17
    @6
    @2
    wcel
    #
    @9
    wi
    #
    vx
    wal
    @3
    @16
    @19
    vx
    @16
    @13
    vf
    wex
    #
    @9
    wi
    @19
    @13
    @9
    vf
    19.23v
    @18
    @20
    @9
    vf
    @6
    chli
    @1
    vx
    vex
    elima2
    imbi1i
    bitr4i
    albii
    vx
    @2
    cH
    dfss2
    bitr4i
    bitri
    @0
    @14
    @10
    vf
    vx
    @0
    @13
    @8
    @9
    @0
    @12
    @5
    @7
    @0
    cn
    cvv
    wcel
    @12
    @5
    wb
    nnex
    cH
    cn
    @4
    csh
    cvv
    elmapg
    mpan2
    anbi1d
    imbi1d
    2albidv
    syl5bbr
    pm5.32i
    bitri
end
