include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wsb.mm"
include "wi.mm"
include "wex.mm"
include "wel.mm"
include "wa.mm"
include "wb.mm"
include "axrep2.mm"
include "nfnae.mm"
include "wnf.mm"
include "nfs1v.mm"
include "a1i.mm"
include "cv.mm"
include "nfcvd.mm"
include "nfcvf2.mm"
include "nfeqd.mm"
include "nfimd.mm"
include "sbequ12r.mm"
include "equequ1.mm"
include "imbi12d.mm"
include "cbvald.mm"
include "exbid.mm"
include "nfvd.mm"
include "nfcrd.mm"
include "nfald.mm"
include "nfand.mm"
include "nfexd.mm"
include "nfbid.mm"
include "elequ1.mm"
include "adantl.mm"
include "nfeqf2.mm"
include "nfan1.mm"
include "albid.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "bibi12d.mm"
include "ex.mm"
include "mpbii.mm"

theorem axrepndlem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x z
  disjoint x y
  disjoint w x
  disjoint w z
  disjoint w y
  disjoint ph w
  assert |- ( -. A. y y = z -> E. x ( E. y A. z ( ph -> z = y ) -> A. z ( z e. x <-> E. x ( x e. y /\ A. y ph ) ) ) )

  proof
    vy
    vz
    weq
    vy
    wal
    wn
    #
    wph
    vz
    vw
    wsb
    #
    vw
    vy
    weq
    #
    wi
    #
    vw
    wal
    #
    vy
    wex
    #
    vw
    vx
    wel
    #
    vx
    vy
    wel
    #
    @1
    vy
    wal
    #
    wa
    #
    vx
    wex
    #
    wb
    #
    vw
    wal
    #
    wi
    #
    vx
    wex
    wph
    vz
    vy
    weq
    #
    wi
    #
    vz
    wal
    #
    vy
    wex
    #
    vz
    vx
    wel
    #
    @7
    wph
    vy
    wal
    #
    wa
    #
    vx
    wex
    #
    wb
    #
    vz
    wal
    #
    wi
    #
    vx
    wex
    @1
    vx
    vy
    vw
    axrep2
    @0
    @13
    @24
    vx
    vy
    vz
    vx
    nfnae
    #
    @0
    @5
    @17
    @12
    @23
    @0
    @4
    @16
    vy
    vy
    vz
    vy
    nfnae
    #
    @0
    @3
    @15
    vw
    vz
    vy
    vz
    vz
    nfnae
    #
    @0
    @1
    @2
    vz
    @1
    vz
    wnf
    @0
    wph
    vz
    vw
    nfs1v
    a1i
    #
    @0
    vz
    vw
    cv
    #
    vy
    cv
    #
    @0
    vz
    @29
    nfcvd
    vy
    vz
    nfcvf2
    #
    nfeqd
    nfimd
    vw
    vz
    weq
    #
    @3
    @15
    wb
    wi
    @0
    @32
    @1
    wph
    @2
    @14
    wph
    vw
    vz
    sbequ12r
    #
    vw
    vz
    vy
    equequ1
    imbi12d
    a1i
    cbvald
    exbid
    @0
    @11
    @22
    vw
    vz
    @27
    @0
    @6
    @10
    vz
    @0
    @6
    vz
    nfvd
    @0
    @9
    vz
    vx
    @25
    @0
    @7
    @8
    vz
    @0
    vz
    vx
    @30
    @31
    nfcrd
    @0
    @1
    vz
    vy
    @26
    @28
    nfald
    nfand
    nfexd
    nfbid
    @0
    @32
    @11
    @22
    wb
    @0
    @32
    wa
    #
    @6
    @18
    @10
    @21
    @32
    @6
    @18
    wb
    @0
    vw
    vz
    vx
    elequ1
    adantl
    @34
    @9
    @20
    vx
    @34
    @8
    @19
    @7
    @34
    @1
    wph
    vy
    @0
    @32
    vy
    @26
    vy
    vz
    vw
    nfeqf2
    nfan1
    @32
    @1
    wph
    wb
    @0
    @33
    adantl
    albid
    anbi2d
    exbidv
    bibi12d
    ex
    cbvald
    imbi12d
    exbid
    mpbii
end
