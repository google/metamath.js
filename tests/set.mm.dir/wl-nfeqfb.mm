include "weq.mm"
include "wnf.mm"
include "wal.mm"
include "wb.mm"
include "wa.mm"
include "nf5r.mm"
include "imp.mm"
include "wl-aleq.mm"
include "simprbi.mm"
include "syl.mm"
include "wn.mm"
include "w3a.mm"
include "nfnt.mm"
include "nf5rd.mm"
include "w3o.mm"
include "wex.mm"
include "alnex.mm"
include "wl-exeq.mm"
include "xchbinx.mm"
include "3ioran.mm"
include "sylbb.mm"
include "3simpc.mm"
include "pm5.21.mm"
include "4syl.mm"
include "pm2.61dan.mm"
include "ax7.mm"
include "al2imi.mm"
include "nftht.mm"
include "syl6.mm"
include "nfeqf.mm"
include "ex.mm"
include "bija.mm"
include "impbii.mm"

theorem wl-nfeqfb
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( F/ x y = z <-> ( A. x x = y <-> A. x x = z ) )

  proof
    vy
    vz
    weq
    #
    vx
    wnf
    #
    vx
    vy
    weq
    #
    vx
    wal
    #
    vx
    vz
    weq
    #
    vx
    wal
    #
    wb
    #
    @1
    @0
    @6
    @1
    @0
    wa
    @0
    vx
    wal
    #
    @6
    @1
    @0
    @7
    @0
    vx
    nf5r
    imp
    @7
    @0
    @6
    vx
    vy
    vz
    wl-aleq
    simprbi
    syl
    @1
    @0
    wn
    #
    wa
    @8
    vx
    wal
    #
    @8
    @3
    wn
    #
    @5
    wn
    #
    w3a
    #
    @10
    @11
    wa
    @6
    @1
    @8
    @9
    @1
    @8
    vx
    @0
    vx
    nfnt
    nf5rd
    imp
    @9
    @0
    @3
    @5
    w3o
    #
    wn
    @12
    @9
    @0
    vx
    wex
    @13
    @0
    vx
    alnex
    vx
    vy
    vz
    wl-exeq
    xchbinx
    @0
    @3
    @5
    3ioran
    sylbb
    @8
    @10
    @11
    3simpc
    @3
    @5
    pm5.21
    4syl
    pm2.61dan
    @3
    @5
    @1
    @3
    @5
    @7
    @1
    @2
    @4
    @0
    vx
    vx
    vy
    vz
    ax7
    al2imi
    @0
    vx
    nftht
    syl6
    @10
    @11
    @1
    vy
    vz
    vx
    nfeqf
    ex
    bija
    impbii
end
