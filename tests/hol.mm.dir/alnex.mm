include "tal.mm"
include "tne.mm"
include "kc.mm"
include "kl.mm"
include "tex.mm"
include "tfal.mm"
include "tim.mm"
include "kbr.mm"
include "wfal.mm"
include "hb.mm"
include "wnot.mm"
include "wc.mm"
include "ax4.mm"
include "ke.mm"
include "ax-cb1.mm"
include "notval.mm"
include "a1i.mm"
include "mpbi.mm"
include "imp.mm"
include "ht.mm"
include "tv.mm"
include "kt.mm"
include "wal.mm"
include "wl.mm"
include "wv.mm"
include "ax-17.mm"
include "ax-hbl1.mm"
include "hbc.mm"
include "exlimd.mm"
include "ex.mm"
include "wex.mm"
include "mpbir.mm"
include "19.8a.mm"
include "wtru.mm"
include "adantl.mm"
include "con3d.mm"
include "trul.mm"
include "alrimi.mm"
include "dedi.mm"

theorem alnex
  param hal: type al
  param vx: var x
  param ta: term A
  let vy: var y
  assume alnex1.1: |- A : bool

  disjoint al x
  disjoint A y
  disjoint x y
  disjoint al y
  assert |- T. |= [ ( ! \ x : al . ( ~ A ) ) = ( ~ ( ? \ x : al . A ) ) ]

  proof
    tal
    hal
    vx
    tne
    ta
    kc
    #
    kl
    #
    kc
    #
    tne
    tex
    hal
    vx
    ta
    kl
    #
    kc
    #
    kc
    #
    @4
    tfal
    tim
    kbr
    #
    @5
    @2
    @2
    @4
    tfal
    hal
    vx
    vy
    ta
    @2
    tfal
    @2
    ta
    tfal
    alnex1.1
    wfal
    @0
    ta
    tfal
    tim
    kbr
    #
    @2
    hal
    vx
    @0
    hb
    hb
    tne
    ta
    wnot
    alnex1.1
    wc
    #
    ax4
    #
    @0
    @7
    ke
    kbr
    @2
    @0
    @2
    @9
    ax-cb1
    #
    ta
    alnex1.1
    notval
    a1i
    mpbi
    imp
    hal
    hal
    hb
    ht
    #
    hb
    vx
    @1
    hal
    vy
    tv
    #
    tal
    kt
    hal
    wal
    #
    hal
    hb
    vx
    @0
    @8
    wl
    hal
    vy
    wv
    #
    hal
    @11
    hb
    ht
    #
    vx
    tal
    @12
    @13
    @14
    ax-17
    hal
    hal
    hb
    vx
    @0
    @12
    @8
    @14
    ax-hbl1
    hbc
    hal
    hb
    vx
    tfal
    @12
    wfal
    @14
    ax-17
    exlimd
    ex
    @5
    @6
    ke
    kbr
    @2
    @10
    @4
    @11
    hb
    tex
    @3
    hal
    wex
    #
    hal
    hb
    vx
    ta
    alnex1.1
    wl
    #
    wc
    #
    notval
    a1i
    mpbir
    hal
    vx
    vy
    @0
    @5
    @5
    @0
    kt
    ta
    @4
    ta
    kt
    @4
    hal
    vx
    ta
    alnex1.1
    19.8a
    wtru
    adantl
    con3d
    trul
    hal
    hb
    hb
    vx
    @4
    @12
    tne
    kt
    wnot
    @18
    @14
    hal
    hb
    hb
    ht
    vx
    tne
    @12
    wnot
    @14
    ax-17
    hal
    @11
    hb
    vx
    @3
    @12
    tex
    kt
    @16
    @17
    @14
    hal
    @15
    vx
    tex
    @12
    @16
    @14
    ax-17
    hal
    hal
    hb
    vx
    ta
    @12
    alnex1.1
    @14
    ax-hbl1
    hbc
    hbc
    alrimi
    dedi
end
