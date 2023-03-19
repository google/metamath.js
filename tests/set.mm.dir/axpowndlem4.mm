include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wel.mm"
include "wex.mm"
include "wi.mm"
include "wa.mm"
include "axpowndlem3.mm"
include "ax-gen.mm"
include "nfnae.mm"
include "nfan.mm"
include "cv.mm"
include "wnfc.mm"
include "nfcvf.mm"
include "adantr.mm"
include "nfcvd.mm"
include "nfeqd.mm"
include "nfnd.mm"
include "nfv.mm"
include "nfeld.mm"
include "nfexd.mm"
include "adantl.mm"
include "nfald.mm"
include "nfimd.mm"
include "wb.mm"
include "equequ2.mm"
include "notbid.mm"
include "nfcvf2.mm"
include "nfan1.mm"
include "elequ2.mm"
include "exbid.mm"
include "biidd.mm"
include "a1i.mm"
include "cbvald.mm"
include "imbi12d.mm"
include "albid.mm"
include "elequ1.mm"
include "ex.mm"
include "mpbii.mm"
include "19.21bi.mm"

theorem axpowndlem4
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( -. A. y y = x -> ( -. A. y y = z -> ( -. x = y -> E. x A. y ( A. x ( E. z x e. y -> A. y x e. z ) -> y e. x ) ) ) )

  proof
    vy
    vx
    weq
    vy
    wal
    wn
    #
    vy
    vz
    weq
    vy
    wal
    wn
    #
    vx
    vy
    weq
    #
    wn
    #
    vx
    vy
    wel
    #
    vz
    wex
    #
    vx
    vz
    wel
    #
    vy
    wal
    #
    wi
    #
    vx
    wal
    #
    vy
    vx
    wel
    #
    wi
    #
    vy
    wal
    #
    vx
    wex
    #
    wi
    #
    @0
    @1
    wa
    #
    @14
    vy
    @15
    vx
    vw
    weq
    #
    wn
    #
    vx
    vw
    wel
    #
    vz
    wex
    #
    @6
    vw
    wal
    #
    wi
    #
    vx
    wal
    #
    vw
    vx
    wel
    #
    wi
    #
    vw
    wal
    #
    vx
    wex
    #
    wi
    #
    vw
    wal
    @14
    vy
    wal
    @27
    vw
    vx
    vw
    vz
    axpowndlem3
    ax-gen
    @15
    @27
    @14
    vw
    vy
    @0
    @1
    vy
    vy
    vx
    vy
    nfnae
    vy
    vz
    vy
    nfnae
    nfan
    #
    @15
    @17
    @26
    vy
    @15
    @16
    vy
    @15
    vy
    vx
    cv
    #
    vw
    cv
    #
    @0
    vy
    @29
    wnfc
    @1
    vy
    vx
    nfcvf
    adantr
    #
    @15
    vy
    @30
    nfcvd
    #
    nfeqd
    nfnd
    @15
    @25
    vy
    vx
    @0
    @1
    vx
    vy
    vx
    vx
    nfnae
    vy
    vz
    vx
    nfnae
    nfan
    #
    @15
    @24
    vy
    vw
    @15
    vw
    nfv
    #
    @15
    @22
    @23
    vy
    @15
    @21
    vy
    vx
    @33
    @15
    @19
    @20
    vy
    @15
    @18
    vy
    vz
    @0
    @1
    vz
    vy
    vx
    vz
    nfnae
    vy
    vz
    vz
    nfnae
    nfan
    #
    @15
    vy
    @29
    @30
    @31
    @32
    nfeld
    nfexd
    @15
    @6
    vy
    vw
    @34
    @15
    vy
    @29
    vz
    cv
    #
    @31
    @1
    vy
    @36
    wnfc
    @0
    vy
    vz
    nfcvf
    adantl
    nfeld
    #
    nfald
    nfimd
    nfald
    @15
    vy
    @30
    @29
    @32
    @31
    nfeld
    nfimd
    #
    nfald
    nfexd
    nfimd
    @15
    vw
    vy
    weq
    #
    @27
    @14
    wb
    @15
    @39
    wa
    #
    @17
    @3
    @26
    @13
    @39
    @17
    @3
    wb
    @15
    @39
    @16
    @2
    vw
    vy
    vx
    equequ2
    notbid
    adantl
    @15
    @26
    @13
    wb
    @39
    @15
    @25
    @12
    vx
    @33
    @15
    @24
    @11
    vw
    vy
    @28
    @38
    @15
    @39
    @24
    @11
    wb
    @40
    @22
    @9
    @23
    @10
    @40
    @21
    @8
    vx
    @15
    @39
    vx
    @33
    @15
    vx
    @30
    vy
    cv
    #
    @15
    vx
    @30
    nfcvd
    @0
    vx
    @41
    wnfc
    @1
    vy
    vx
    nfcvf2
    adantr
    nfeqd
    nfan1
    @40
    @19
    @5
    @20
    @7
    @40
    @18
    @4
    vz
    @15
    @39
    vz
    @35
    @15
    vz
    @30
    @41
    @15
    vz
    @30
    nfcvd
    @1
    vz
    @41
    wnfc
    @0
    vy
    vz
    nfcvf2
    adantl
    nfeqd
    nfan1
    @39
    @18
    @4
    wb
    @15
    vw
    vy
    vx
    elequ2
    adantl
    exbid
    @15
    @20
    @7
    wb
    @39
    @15
    @6
    @6
    vw
    vy
    @28
    @37
    @39
    @6
    @6
    wb
    wi
    @15
    @39
    @6
    biidd
    a1i
    cbvald
    adantr
    imbi12d
    albid
    @39
    @23
    @10
    wb
    @15
    vw
    vy
    vx
    elequ1
    adantl
    imbi12d
    ex
    cbvald
    exbid
    adantr
    imbi12d
    ex
    cbvald
    mpbii
    19.21bi
    ex
end
