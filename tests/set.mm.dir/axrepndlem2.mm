include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wex.mm"
include "wel.mm"
include "wb.mm"
include "wsb.mm"
include "axrepndlem1.mm"
include "nfnae.mm"
include "nfan.mm"
include "wnf.mm"
include "nfs1v.mm"
include "a1i.mm"
include "cv.mm"
include "wnfc.mm"
include "nfcvf.mm"
include "adantl.mm"
include "adantr.mm"
include "nfeqd.mm"
include "nfimd.mm"
include "nfald.mm"
include "nfexd.mm"
include "nfcvd.mm"
include "nfeld.mm"
include "nfv.mm"
include "nfand.mm"
include "nfbid.mm"
include "nfcvf2.mm"
include "nfan1.mm"
include "sbequ12r.mm"
include "imbi1d.mm"
include "albid.mm"
include "exbid.mm"
include "elequ2.mm"
include "elequ1.mm"
include "anbi12d.mm"
include "ex.mm"
include "cbvexd.mm"
include "bibi12d.mm"
include "imbi12d.mm"
include "syl5ib.mm"
include "imp.mm"

theorem axrepndlem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ( ( -. A. x x = y /\ -. A. x x = z ) /\ -. A. y y = z ) -> E. x ( E. y A. z ( ph -> z = y ) -> A. z ( z e. x <-> E. x ( x e. y /\ A. y ph ) ) ) )

  proof
    vx
    vy
    weq
    vx
    wal
    wn
    #
    vx
    vz
    weq
    vx
    wal
    wn
    #
    wa
    #
    vy
    vz
    weq
    vy
    wal
    wn
    #
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
    vx
    vy
    wel
    #
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
    #
    @3
    wph
    vx
    vw
    wsb
    #
    @4
    wi
    #
    vz
    wal
    #
    vy
    wex
    #
    vz
    vw
    wel
    #
    vw
    vy
    wel
    #
    @17
    vy
    wal
    #
    wa
    #
    vw
    wex
    #
    wb
    #
    vz
    wal
    #
    wi
    #
    vw
    wex
    @2
    @16
    @17
    vw
    vy
    vz
    axrepndlem1
    @2
    @28
    @15
    vw
    vx
    @0
    @1
    vx
    vx
    vy
    vx
    nfnae
    vx
    vz
    vx
    nfnae
    nfan
    #
    @2
    @20
    @27
    vx
    @2
    @19
    vx
    vy
    @0
    @1
    vy
    vx
    vy
    vy
    nfnae
    vx
    vz
    vy
    nfnae
    nfan
    #
    @2
    @18
    vx
    vz
    @0
    @1
    vz
    vx
    vy
    vz
    nfnae
    vx
    vz
    vz
    nfnae
    nfan
    #
    @2
    @17
    @4
    vx
    @17
    vx
    wnf
    @2
    wph
    vx
    vw
    nfs1v
    a1i
    #
    @2
    vx
    vz
    cv
    #
    vy
    cv
    #
    @1
    vx
    @33
    wnfc
    @0
    vx
    vz
    nfcvf
    adantl
    #
    @0
    vx
    @34
    wnfc
    @1
    vx
    vy
    nfcvf
    adantr
    #
    nfeqd
    nfimd
    nfald
    nfexd
    @2
    @26
    vx
    vz
    @31
    @2
    @21
    @25
    vx
    @2
    vx
    @33
    vw
    cv
    #
    @35
    @2
    vx
    @37
    nfcvd
    #
    nfeld
    @2
    @24
    vx
    vw
    @2
    vw
    nfv
    @2
    @22
    @23
    vx
    @2
    vx
    @37
    @34
    @38
    @36
    nfeld
    @2
    @17
    vx
    vy
    @30
    @32
    nfald
    nfand
    #
    nfexd
    nfbid
    nfald
    nfimd
    @2
    vw
    vx
    weq
    #
    @28
    @15
    wb
    @2
    @40
    wa
    #
    @20
    @7
    @27
    @14
    @41
    @19
    @6
    vy
    @2
    @40
    vy
    @30
    @2
    vy
    @37
    vx
    cv
    #
    @2
    vy
    @37
    nfcvd
    @0
    vy
    @42
    wnfc
    @1
    vx
    vy
    nfcvf2
    adantr
    nfeqd
    nfan1
    #
    @41
    @18
    @5
    vz
    @2
    @40
    vz
    @31
    @2
    vz
    @37
    @42
    @2
    vz
    @37
    nfcvd
    @1
    vz
    @42
    wnfc
    @0
    vx
    vz
    nfcvf2
    adantl
    nfeqd
    nfan1
    #
    @40
    @18
    @5
    wb
    @2
    @40
    @17
    wph
    @4
    wph
    vw
    vx
    sbequ12r
    #
    imbi1d
    adantl
    albid
    exbid
    @41
    @26
    @13
    vz
    @44
    @41
    @21
    @8
    @25
    @12
    @40
    @21
    @8
    wb
    @2
    vw
    vx
    vz
    elequ2
    adantl
    @2
    @25
    @12
    wb
    @40
    @2
    @24
    @11
    vw
    vx
    @29
    @39
    @2
    @40
    @24
    @11
    wb
    @41
    @22
    @9
    @23
    @10
    @40
    @22
    @9
    wb
    @2
    vw
    vx
    vy
    elequ1
    adantl
    @41
    @17
    wph
    vy
    @43
    @40
    @17
    wph
    wb
    @2
    @45
    adantl
    albid
    anbi12d
    ex
    cbvexd
    adantr
    bibi12d
    albid
    imbi12d
    ex
    cbvexd
    syl5ib
    imp
end
