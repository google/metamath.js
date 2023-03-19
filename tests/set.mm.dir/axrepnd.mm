include "weq.mm"
include "wal.mm"
include "wi.mm"
include "wex.mm"
include "wel.mm"
include "wa.mm"
include "wb.mm"
include "wn.mm"
include "axrepndlem2.mm"
include "nfnae.mm"
include "nfan.mm"
include "cv.mm"
include "wnfc.mm"
include "nfcvf.mm"
include "adantl.mm"
include "nfcvf2.mm"
include "ad2antrr.mm"
include "nfeld.mm"
include "nf5rd.mm"
include "sp.mm"
include "impbid1.mm"
include "ad2antlr.mm"
include "anbi1d.mm"
include "exbid.mm"
include "bibi12d.mm"
include "albid.mm"
include "imbi2d.mm"
include "mpbid.mm"
include "exp31.mm"
include "nfae.mm"
include "nd2.mm"
include "aecoms.mm"
include "nd3.mm"
include "intnanrd.mm"
include "nexd.mm"
include "2falsed.mm"
include "alrimi.mm"
include "a1d.mm"
include "19.8a.mm"
include "syl.mm"
include "nd4.mm"
include "nd1.mm"
include "pm2.61iii.mm"

theorem axrepnd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- E. x ( E. y A. z ( ph -> z = y ) -> A. z ( A. y z e. x <-> E. x ( A. z x e. y /\ A. y ph ) ) )

  proof
    vx
    vy
    weq
    vx
    wal
    #
    vx
    vz
    weq
    vx
    wal
    #
    vy
    vz
    weq
    vy
    wal
    #
    wph
    vz
    vy
    weq
    wi
    vz
    wal
    vy
    wex
    #
    vz
    vx
    wel
    #
    vy
    wal
    #
    vx
    vy
    wel
    #
    vz
    wal
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
    @0
    wn
    #
    @1
    wn
    #
    @2
    wn
    #
    @14
    @15
    @16
    wa
    #
    @17
    wa
    #
    @3
    @4
    @6
    @8
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
    @14
    wph
    vx
    vy
    vz
    axrepndlem2
    @19
    @24
    @13
    vx
    @18
    @17
    vx
    @15
    @16
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
    vy
    vz
    vx
    nfnae
    nfan
    #
    @19
    @23
    @12
    @3
    @19
    @22
    @11
    vz
    @18
    @17
    vz
    @15
    @16
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
    vy
    vz
    vz
    nfnae
    nfan
    @19
    @4
    @5
    @21
    @10
    @19
    @4
    @5
    @19
    @4
    vy
    @19
    vy
    vz
    cv
    #
    vx
    cv
    #
    @17
    vy
    @26
    wnfc
    @18
    vy
    vz
    nfcvf
    adantl
    @15
    vy
    @27
    wnfc
    @16
    @17
    vx
    vy
    nfcvf2
    ad2antrr
    nfeld
    nf5rd
    @4
    vy
    sp
    impbid1
    @19
    @20
    @9
    vx
    @25
    @19
    @6
    @7
    @8
    @19
    @6
    @7
    @19
    @6
    vz
    @19
    vz
    @27
    vy
    cv
    #
    @16
    vz
    @27
    wnfc
    @15
    @17
    vx
    vz
    nfcvf2
    ad2antlr
    @17
    vz
    @28
    wnfc
    @18
    vy
    vz
    nfcvf2
    adantl
    nfeld
    nf5rd
    @6
    vz
    sp
    impbid1
    anbi1d
    exbid
    bibi12d
    albid
    imbi2d
    exbid
    mpbid
    exp31
    @0
    @13
    @14
    @0
    @12
    @3
    @0
    @11
    vz
    vx
    vy
    vz
    nfae
    @0
    @5
    @10
    @5
    wn
    vy
    vx
    vy
    vx
    vz
    nd2
    aecoms
    @0
    @9
    vx
    vx
    vy
    vx
    nfae
    @0
    @7
    @8
    vx
    vy
    vz
    nd3
    intnanrd
    nexd
    2falsed
    alrimi
    a1d
    @13
    vx
    19.8a
    #
    syl
    @1
    @13
    @14
    @1
    @12
    @3
    @1
    @11
    vz
    vx
    vz
    vz
    nfae
    @1
    @5
    @10
    vx
    vz
    vy
    nd4
    @1
    @9
    vx
    vx
    vz
    vx
    nfae
    @1
    @7
    @8
    @7
    wn
    #
    vz
    vx
    vz
    vx
    vy
    nd1
    aecoms
    intnanrd
    nexd
    2falsed
    alrimi
    a1d
    @29
    syl
    @2
    @13
    @14
    @2
    @12
    @3
    @2
    @11
    vz
    vy
    vz
    vz
    nfae
    @2
    @5
    @10
    vy
    vz
    vx
    nd1
    @2
    @9
    vx
    vy
    vz
    vx
    nfae
    @2
    @7
    @8
    @30
    vz
    vy
    vz
    vy
    vx
    nd2
    aecoms
    intnanrd
    nexd
    2falsed
    alrimi
    a1d
    @29
    syl
    pm2.61iii
end
