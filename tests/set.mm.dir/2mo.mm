include "weq.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wsb.mm"
include "wmo.mm"
include "2mo2.mm"
include "nfmo1.mm"
include "nfe1.mm"
include "nfmo.mm"
include "nfan.mm"
include "19.8a.mm"
include "spsbe.mm"
include "sbimi.mm"
include "nfv.mm"
include "mo3.mm"
include "biimpi.mm"
include "19.21bbi.mm"
include "syl2ani.mm"
include "sbcom2.mm"
include "sylbi.mm"
include "anim12ii.mm"
include "alrimi.mm"
include "alrimivv.mm"
include "sylbir.mm"
include "nfs1v.mm"
include "nfsb.mm"
include "pm3.21.mm"
include "imim1d.mm"
include "alimd.mm"
include "com12.mm"
include "aleximi.mm"
include "wn.mm"
include "2nexaln.mm"
include "2sb8e.mm"
include "xchnxbi.mm"
include "pm2.21.mm"
include "2alimi.mm"
include "2eximi.mm"
include "19.23bi.mm"
include "pm2.61d1.mm"
include "impbii.mm"
include "alrot4.mm"
include "bitri.mm"

theorem 2mo
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint ph z
  disjoint ph w
  assert |- ( E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) <-> A. x A. y A. z A. w ( ( ph /\ [ z / x ] [ w / y ] ph ) -> ( x = z /\ y = w ) ) )

  proof
    wph
    vx
    vz
    weq
    #
    vy
    vw
    weq
    #
    wa
    #
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    vw
    wex
    #
    vz
    wex
    #
    wph
    wph
    vy
    vw
    wsb
    #
    vx
    vz
    wsb
    #
    wa
    #
    @2
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    vw
    wal
    #
    vz
    wal
    #
    @11
    vw
    wal
    vz
    wal
    vy
    wal
    vx
    wal
    @7
    @15
    @7
    wph
    vy
    wex
    #
    vx
    wmo
    #
    wph
    vx
    wex
    #
    vy
    wmo
    #
    wa
    #
    @15
    wph
    vx
    vy
    vz
    vw
    2mo2
    @20
    @13
    vz
    vw
    @20
    @12
    vx
    @17
    @19
    vx
    @16
    vx
    nfmo1
    @18
    vx
    vy
    wph
    vx
    nfe1
    nfmo
    nfan
    @20
    @11
    vy
    @17
    @19
    vy
    @16
    vy
    vx
    wph
    vy
    nfe1
    nfmo
    @18
    vy
    nfmo1
    nfan
    @17
    @10
    @0
    @19
    @1
    wph
    @17
    @16
    @16
    vx
    vz
    wsb
    #
    @0
    @9
    wph
    vy
    19.8a
    @8
    @16
    vx
    vz
    wph
    vy
    vw
    spsbe
    sbimi
    @17
    @16
    @21
    wa
    @0
    wi
    #
    vx
    vz
    @17
    @22
    vz
    wal
    vx
    wal
    @16
    vx
    vz
    @16
    vz
    nfv
    mo3
    biimpi
    19.21bbi
    syl2ani
    wph
    @19
    @18
    @18
    vy
    vw
    wsb
    #
    @1
    @9
    wph
    vx
    19.8a
    @9
    wph
    vx
    vz
    wsb
    #
    vy
    vw
    wsb
    @23
    wph
    vy
    vw
    vx
    vz
    sbcom2
    @24
    @18
    vy
    vw
    wph
    vx
    vz
    spsbe
    sbimi
    sylbi
    @19
    @18
    @23
    wa
    @1
    wi
    #
    vy
    vw
    @19
    @25
    vw
    wal
    vy
    wal
    @18
    vy
    vw
    @18
    vw
    nfv
    mo3
    biimpi
    19.21bbi
    syl2ani
    anim12ii
    alrimi
    alrimi
    alrimivv
    sylbir
    @15
    @9
    vw
    wex
    #
    vz
    wex
    #
    @7
    @14
    @26
    @6
    vz
    @13
    @9
    @5
    vw
    @9
    @13
    @5
    @9
    @12
    @4
    vx
    @8
    vx
    vz
    nfs1v
    @9
    @11
    @3
    vy
    @8
    vx
    vz
    vy
    wph
    vy
    vw
    nfs1v
    nfsb
    @9
    wph
    @10
    @2
    @9
    wph
    pm3.21
    imim1d
    alimd
    alimd
    com12
    aleximi
    aleximi
    @27
    wn
    wph
    wn
    #
    vy
    wal
    vx
    wal
    #
    @7
    @16
    vx
    wex
    @29
    @27
    wph
    vx
    vy
    2nexaln
    wph
    vx
    vy
    vz
    vw
    2sb8e
    xchnxbi
    @29
    @7
    vw
    @29
    vw
    wex
    @7
    vz
    @29
    @5
    vz
    vw
    @28
    @3
    vx
    vy
    wph
    @2
    pm2.21
    2alimi
    2eximi
    19.23bi
    19.23bi
    sylbi
    pm2.61d1
    impbii
    @11
    vz
    vw
    vx
    vy
    alrot4
    bitri
end
