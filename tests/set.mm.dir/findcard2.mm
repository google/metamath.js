include "cfn.mm"
include "cv.mm"
include "wcel.mm"
include "cen.mm"
include "wbr.mm"
include "com.mm"
include "wrex.mm"
include "isfi.mm"
include "wi.mm"
include "wal.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "breq2.mm"
include "imbi1d.mm"
include "albidv.mm"
include "weq.mm"
include "en0.mm"
include "mpbiri.mm"
include "sylbi.mm"
include "ax-gen.mm"
include "wsbc.mm"
include "wne.mm"
include "wa.mm"
include "nsuceq0.mm"
include "breq1.mm"
include "anbi2d.mm"
include "wb.mm"
include "peano1.mm"
include "peano2.mm"
include "nneneq.mm"
include "sylancr.mm"
include "biimpa.mm"
include "eqcomd.mm"
include "syl6bi.mm"
include "com12.mm"
include "necon3d.mm"
include "mpi.mm"
include "ex.mm"
include "wel.mm"
include "wex.mm"
include "n0.mm"
include "csn.mm"
include "cdif.mm"
include "dif1en.mm"
include "3expia.mm"
include "wss.mm"
include "cun.mm"
include "snssi.mm"
include "uncom.mm"
include "undif.mm"
include "biimpi.mm"
include "syl5eq.mm"
include "cvv.mm"
include "vex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "uneq1.mm"
include "sbceq1d.mm"
include "imbi2d.mm"
include "imbi12d.mm"
include "spv.mm"
include "rspe.mm"
include "sylibr.mm"
include "pm2.27.mm"
include "adantl.mm"
include "sylsyld.mm"
include "syl5.mm"
include "snex.mm"
include "unex.mm"
include "sbcie.mm"
include "syl6ibr.mm"
include "vtocl.mm"
include "dfsbcq.mm"
include "syl5ib.mm"
include "3syl.mm"
include "expd.mm"
include "adantr.mm"
include "mpdd.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "com23.mm"
include "alrimdv.mm"
include "nfv.mm"
include "nfsbc1v.mm"
include "nfim.mm"
include "sbceq1a.mm"
include "cbval.mm"
include "finds1.mm"
include "19.21bi.mm"
include "rexlimiv.mm"
include "vtoclga.mm"

theorem findcard2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vv: setvar v
  let vw: setvar w
  assume findcard2.1: |- ( x = (/) -> ( ph <-> ps ) )
  assume findcard2.2: |- ( x = y -> ( ph <-> ch ) )
  assume findcard2.3: |- ( x = ( y u. { z } ) -> ( ph <-> th ) )
  assume findcard2.4: |- ( x = A -> ( ph <-> ta ) )
  assume findcard2.5: |- ps
  assume findcard2.6: |- ( y e. Fin -> ( ch -> th ) )

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint ps x
  disjoint ch x
  disjoint th x
  disjoint ta x
  disjoint ph y
  disjoint ph z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint ph v
  disjoint ph w
  assert |- ( A e. Fin -> ta )

  proof
    wph
    wta
    vx
    cA
    cfn
    findcard2.4
    vx
    cv
    #
    cfn
    wcel
    @0
    vw
    cv
    #
    cen
    wbr
    #
    vw
    com
    wrex
    wph
    vw
    @0
    isfi
    @2
    wph
    vw
    com
    @1
    com
    wcel
    @2
    wph
    wi
    #
    vx
    @3
    vx
    wal
    @0
    c0
    cen
    wbr
    #
    wph
    wi
    #
    vx
    wal
    @0
    vv
    cv
    #
    cen
    wbr
    #
    wph
    wi
    #
    vx
    wal
    #
    @0
    @6
    csuc
    #
    cen
    wbr
    #
    wph
    wi
    #
    vx
    wal
    #
    vw
    vv
    @1
    c0
    wceq
    #
    @3
    @5
    vx
    @14
    @2
    @4
    wph
    @1
    c0
    @0
    cen
    breq2
    imbi1d
    albidv
    vw
    vv
    weq
    #
    @3
    @8
    vx
    @15
    @2
    @7
    wph
    @1
    @6
    @0
    cen
    breq2
    imbi1d
    albidv
    @1
    @10
    wceq
    #
    @3
    @12
    vx
    @16
    @2
    @11
    wph
    @1
    @10
    @0
    cen
    breq2
    imbi1d
    albidv
    @5
    vx
    @4
    @0
    c0
    wceq
    #
    wph
    @0
    en0
    @17
    wph
    wps
    findcard2.5
    findcard2.1
    mpbiri
    sylbi
    ax-gen
    @6
    com
    wcel
    #
    @9
    @1
    @10
    cen
    wbr
    #
    wph
    vx
    @1
    wsbc
    #
    wi
    #
    vw
    wal
    @13
    @18
    @9
    @21
    vw
    @18
    @19
    @9
    @20
    @18
    @19
    @1
    c0
    wne
    #
    @9
    @20
    wi
    #
    @18
    @19
    @22
    @18
    @19
    wa
    #
    @10
    c0
    wne
    @22
    @6
    nsuceq0
    @24
    @1
    c0
    @10
    c0
    @14
    @24
    @10
    c0
    wceq
    #
    @14
    @24
    @18
    c0
    @10
    cen
    wbr
    #
    wa
    #
    @25
    @14
    @19
    @26
    @18
    @1
    c0
    @10
    cen
    breq1
    anbi2d
    @27
    c0
    @10
    @18
    @26
    c0
    @10
    wceq
    #
    @18
    c0
    com
    wcel
    @10
    com
    wcel
    @26
    @28
    wb
    peano1
    @6
    peano2
    c0
    @10
    nneneq
    sylancr
    biimpa
    eqcomd
    syl6bi
    com12
    necon3d
    mpi
    ex
    @18
    @19
    @22
    @23
    wi
    @22
    vz
    vw
    wel
    #
    vz
    wex
    @24
    @23
    vz
    @1
    n0
    @24
    @29
    @23
    vz
    @24
    @29
    @1
    vz
    cv
    #
    csn
    #
    cdif
    #
    @6
    cen
    wbr
    #
    @23
    @18
    @19
    @29
    @33
    @1
    @6
    @30
    dif1en
    3expia
    @18
    @29
    @33
    @23
    wi
    #
    wi
    @19
    @29
    @18
    @34
    @29
    @18
    @33
    @23
    @29
    @31
    @1
    wss
    #
    @32
    @31
    cun
    #
    @1
    wceq
    #
    @18
    @33
    wa
    #
    @23
    wi
    @30
    @1
    snssi
    @35
    @36
    @31
    @32
    cun
    #
    @1
    @32
    @31
    uncom
    @35
    @39
    @1
    wceq
    @31
    @1
    undif
    biimpi
    syl5eq
    @38
    @9
    wph
    vx
    @36
    wsbc
    #
    wi
    #
    @37
    @23
    @18
    vy
    cv
    #
    @6
    cen
    wbr
    #
    wa
    #
    @9
    wph
    vx
    @42
    @31
    cun
    #
    wsbc
    #
    wi
    #
    wi
    @38
    @41
    wi
    vy
    @32
    @1
    cvv
    wcel
    @32
    cvv
    wcel
    vw
    vex
    @1
    @31
    cvv
    difexg
    ax-mp
    @42
    @32
    wceq
    #
    @44
    @38
    @47
    @41
    @48
    @43
    @33
    @18
    @42
    @32
    @6
    cen
    breq1
    anbi2d
    @48
    @46
    @40
    @9
    @48
    wph
    vx
    @45
    @36
    @42
    @32
    @31
    uneq1
    sbceq1d
    imbi2d
    imbi12d
    @44
    @9
    wth
    @46
    @9
    @43
    wch
    wi
    #
    @44
    wth
    @8
    @49
    vx
    vy
    vx
    vy
    weq
    @7
    @43
    wph
    wch
    @0
    @42
    @6
    cen
    breq1
    findcard2.2
    imbi12d
    spv
    @44
    @42
    cfn
    wcel
    #
    @49
    wch
    wth
    @44
    @43
    vv
    com
    wrex
    @50
    @43
    vv
    com
    rspe
    vv
    @42
    isfi
    sylibr
    @43
    @49
    wch
    wi
    @18
    @43
    wch
    pm2.27
    adantl
    findcard2.6
    sylsyld
    syl5
    wph
    wth
    vx
    @45
    @42
    @31
    vy
    vex
    @30
    snex
    unex
    findcard2.3
    sbcie
    syl6ibr
    vtocl
    @37
    @40
    @20
    @9
    wph
    vx
    @36
    @1
    dfsbcq
    imbi2d
    syl5ib
    3syl
    expd
    com12
    adantr
    mpdd
    exlimdv
    syl5bi
    ex
    mpdd
    com23
    alrimdv
    @12
    @21
    vx
    vw
    @12
    vw
    nfv
    @19
    @20
    vx
    @19
    vx
    nfv
    wph
    vx
    @1
    nfsbc1v
    nfim
    vx
    vw
    weq
    @11
    @19
    wph
    @20
    @0
    @1
    @10
    cen
    breq1
    wph
    vx
    @1
    sbceq1a
    imbi12d
    cbval
    syl6ibr
    finds1
    19.21bi
    rexlimiv
    sylbi
    vtoclga
end
