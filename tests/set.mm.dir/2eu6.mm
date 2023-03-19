include "wex.mm"
include "weu.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "2eu4.mm"
include "nfia1.mm"
include "nfa1.mm"
include "nfv.mm"
include "simpl.mm"
include "imim2i.mm"
include "sps.mm"
include "exlimd.mm"
include "ax12v.mm"
include "syli.mm"
include "com12.mm"
include "spsd.mm"
include "wsb.mm"
include "nfs1v.mm"
include "simpr.mm"
include "sbequ1.mm"
include "imim2d.mm"
include "al2imi.mm"
include "sb6.mm"
include "2sb6.mm"
include "bitr3i.mm"
include "syl6ib.mm"
include "sylcom.mm"
include "ancld.mm"
include "2albiim.mm"
include "syl6ibr.mm"
include "exlimi.mm"
include "2eximdv.mm"
include "imp.mm"
include "biimpr.mm"
include "2alimi.mm"
include "2eximi.mm"
include "2exsb.mm"
include "sylibr.mm"
include "biimp.mm"
include "jca.mm"
include "impbii.mm"
include "bitri.mm"

theorem 2eu6
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
  assert |- ( ( E! x E. y ph /\ E! y E. x ph ) <-> E. z E. w A. x A. y ( ph <-> ( x = z /\ y = w ) ) )

  proof
    wph
    vy
    wex
    #
    vx
    weu
    wph
    vx
    wex
    vy
    weu
    wa
    @0
    vx
    wex
    #
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
    vz
    wex
    #
    wa
    #
    wph
    @4
    wb
    #
    vy
    wal
    #
    vx
    wal
    #
    vw
    wex
    vz
    wex
    #
    wph
    vx
    vy
    vz
    vw
    2eu4
    @9
    @13
    @1
    @8
    @13
    @1
    @7
    @12
    vz
    vw
    @0
    @7
    @12
    wi
    vx
    @6
    @11
    vx
    nfia1
    @0
    @7
    @7
    @4
    wph
    wi
    #
    vy
    wal
    vx
    wal
    #
    wa
    @12
    @0
    @7
    @15
    @0
    @7
    @2
    @0
    wi
    #
    vx
    wal
    #
    @15
    @0
    @6
    @17
    vx
    @6
    @0
    @17
    @0
    @6
    @2
    @17
    @6
    wph
    @2
    vy
    @5
    vy
    nfa1
    #
    @2
    vy
    nfv
    @5
    wph
    @2
    wi
    vy
    @4
    @2
    wph
    @2
    @3
    simpl
    imim2i
    sps
    exlimd
    @0
    vx
    vz
    ax12v
    syli
    com12
    spsd
    @7
    @17
    @2
    wph
    vy
    vw
    wsb
    #
    wi
    #
    vx
    wal
    #
    @15
    @6
    @16
    @20
    vx
    @6
    @0
    @19
    @2
    @6
    wph
    @19
    vy
    @18
    wph
    vy
    vw
    nfs1v
    @5
    wph
    @19
    wi
    vy
    wph
    @5
    @3
    @19
    @4
    @3
    wph
    @2
    @3
    simpr
    imim2i
    wph
    vy
    vw
    sbequ1
    syli
    sps
    exlimd
    imim2d
    al2imi
    @21
    @19
    vx
    vz
    wsb
    @15
    @19
    vx
    vz
    sb6
    wph
    vx
    vy
    vz
    vw
    2sb6
    bitr3i
    syl6ib
    sylcom
    ancld
    wph
    @4
    vx
    vy
    2albiim
    syl6ibr
    exlimi
    2eximdv
    imp
    @13
    @1
    @8
    @13
    @15
    vw
    wex
    vz
    wex
    @1
    @12
    @15
    vz
    vw
    @10
    @14
    vx
    vy
    wph
    @4
    biimpr
    2alimi
    2eximi
    wph
    vx
    vy
    vz
    vw
    2exsb
    sylibr
    @12
    @7
    vz
    vw
    @10
    @5
    vx
    vy
    wph
    @4
    biimp
    2alimi
    2eximi
    jca
    impbii
    bitri
end
