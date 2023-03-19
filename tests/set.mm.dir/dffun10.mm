include "wrel.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "cvv.mm"
include "cid.mm"
include "cdif.mm"
include "ccom.mm"
include "wss.mm"
include "wfun.mm"
include "ssrel.mm"
include "impexp.mm"
include "albii.mm"
include "19.21v.mm"
include "wn.mm"
include "wbr.mm"
include "wex.mm"
include "vex.mm"
include "opelco.mm"
include "df-br.mm"
include "brv.mm"
include "brdif.mm"
include "mpbiran.mm"
include "ideq.mm"
include "equcom.mm"
include "bitri.mm"
include "xchbinx.mm"
include "anbi12i.mm"
include "exbii.mm"
include "exanali.mm"
include "3bitri.mm"
include "con2bii.mm"
include "opex.mm"
include "eldif.mm"
include "bitr4i.mm"
include "imbi2i.mm"
include "2albii.mm"
include "syl6rbbr.mm"
include "pm5.32i.mm"
include "dffun4.mm"
include "sscoid.mm"
include "3bitr4i.mm"

theorem dffun10
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( Fun F <-> F C_ ( _I o. ( _V \ ( ( _V \ _I ) o. F ) ) ) )

  proof
    cF
    wrel
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cF
    wcel
    #
    @1
    vz
    cv
    #
    cop
    cF
    wcel
    #
    wa
    vy
    vz
    weq
    #
    wi
    #
    vz
    wal
    #
    vy
    wal
    vx
    wal
    #
    wa
    @0
    cF
    cvv
    cvv
    cid
    cdif
    #
    cF
    ccom
    #
    cdif
    #
    wss
    #
    wa
    cF
    wfun
    cF
    cid
    @13
    ccom
    wss
    @0
    @10
    @14
    @0
    @14
    @4
    @3
    @13
    wcel
    #
    wi
    #
    vy
    wal
    vx
    wal
    @10
    vx
    vy
    cF
    @13
    ssrel
    @9
    @16
    vx
    vy
    @9
    @4
    @6
    @7
    wi
    #
    wi
    #
    vz
    wal
    @4
    @17
    vz
    wal
    #
    wi
    @16
    @8
    @18
    vz
    @4
    @6
    @7
    impexp
    albii
    @4
    @17
    vz
    19.21v
    @19
    @15
    @4
    @19
    @3
    @12
    wcel
    #
    wn
    #
    @15
    @20
    @19
    @20
    @1
    @5
    cF
    wbr
    #
    @5
    @2
    @11
    wbr
    #
    wa
    #
    vz
    wex
    @6
    @7
    wn
    #
    wa
    #
    vz
    wex
    @19
    wn
    vz
    @1
    @2
    @11
    cF
    vx
    vex
    vy
    vex
    #
    opelco
    @24
    @26
    vz
    @22
    @6
    @23
    @25
    @1
    @5
    cF
    df-br
    @23
    @5
    @2
    cid
    wbr
    #
    @7
    @23
    @5
    @2
    cvv
    wbr
    @28
    wn
    @5
    @2
    brv
    @5
    @2
    cvv
    cid
    brdif
    mpbiran
    @28
    vz
    vy
    weq
    @7
    @5
    @2
    @27
    ideq
    vz
    vy
    equcom
    bitri
    xchbinx
    anbi12i
    exbii
    @6
    @7
    vz
    exanali
    3bitri
    con2bii
    @15
    @3
    cvv
    wcel
    @21
    @1
    @2
    opex
    @3
    cvv
    @12
    eldif
    mpbiran
    bitr4i
    imbi2i
    3bitri
    2albii
    syl6rbbr
    pm5.32i
    vx
    vy
    vz
    cF
    dffun4
    cF
    @13
    sscoid
    3bitr4i
end
