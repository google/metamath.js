include "tex.mm"
include "kl.mm"
include "kc.mm"
include "kct.mm"
include "tal.mm"
include "tv.mm"
include "tim.mm"
include "kbr.mm"
include "ax-cb2.mm"
include "hb.mm"
include "wim.mm"
include "ax-cb1.mm"
include "wctr.mm"
include "wl.mm"
include "wv.mm"
include "wc.mm"
include "wov.mm"
include "wctl.mm"
include "id.mm"
include "kt.mm"
include "ex.mm"
include "wtru.mm"
include "adantl.mm"
include "ht.mm"
include "ax-17.mm"
include "ax-hbl1.mm"
include "hbc.mm"
include "hbov.mm"
include "ke.mm"
include "weqi.mm"
include "beta.mm"
include "eqcomi.mm"
include "a1i.mm"
include "ceq2.mm"
include "eqtri.mm"
include "oveq1.mm"
include "oveq2.mm"
include "insti.mm"
include "mpd.mm"
include "alrimiv.mm"
include "wex.mm"
include "adantr.mm"
include "simpr.mm"
include "exval.mm"
include "mpbi.mm"
include "wal.mm"
include "leq.mm"
include "oveq12.mm"
include "cla4v.mm"
include "syl.mm"

theorem exlimd
  param hal: type al
  param vx: var x
  param vy: var y
  param ta: term A
  param tr: term R
  param tt: term T
  let vz: var z
  assume exlimd.1: |- ( R , A ) |= T
  assume exlimd.2: |- T. |= [ ( \ x : al . R y : al ) = R ]
  assume exlimd.3: |- T. |= [ ( \ x : al . T y : al ) = T ]

  disjoint A y
  disjoint R y
  disjoint T y
  disjoint x y
  disjoint al x
  disjoint al y
  disjoint y z
  disjoint A z
  disjoint R z
  disjoint T z
  disjoint x z
  disjoint al z
  assert |- ( R , ( ? \ x : al . A ) ) |= T

  proof
    tr
    tex
    hal
    vx
    ta
    kl
    #
    kc
    #
    kct
    #
    tal
    hal
    vz
    @0
    hal
    vz
    tv
    #
    kc
    #
    tt
    tim
    kbr
    #
    kl
    #
    kc
    #
    tt
    tt
    tr
    ta
    kct
    #
    exlimd.1
    ax-cb2
    #
    tr
    @1
    @7
    hal
    vz
    @5
    tr
    tr
    tr
    @5
    hb
    hb
    hb
    @4
    tt
    tim
    wim
    hal
    hb
    @0
    @3
    hal
    hb
    vx
    ta
    tr
    ta
    tt
    @8
    exlimd.1
    ax-cb1
    #
    wctr
    #
    wl
    #
    hal
    vz
    wv
    #
    wc
    #
    @9
    wov
    #
    tr
    tr
    ta
    @10
    wctl
    #
    id
    tr
    @5
    tim
    kbr
    #
    tr
    @16
    hal
    vx
    vy
    tr
    ta
    tt
    tim
    kbr
    #
    tim
    kbr
    @17
    @3
    kt
    @13
    hb
    hb
    hb
    tr
    @5
    tim
    wim
    @16
    @15
    wov
    kt
    tr
    @18
    tr
    kt
    @18
    tr
    ta
    tt
    exlimd.1
    ex
    wtru
    adantl
    ex
    hal
    hb
    hb
    hb
    vx
    tr
    hal
    vy
    tv
    #
    @5
    tim
    kt
    wim
    @16
    hal
    vy
    wv
    #
    @15
    hal
    hb
    hb
    hb
    ht
    ht
    vx
    tim
    @19
    wim
    @20
    ax-17
    #
    exlimd.2
    hal
    hb
    hb
    hb
    vx
    @4
    @19
    tt
    tim
    kt
    wim
    @14
    @20
    @9
    @21
    hal
    hal
    hb
    vx
    @3
    @19
    @0
    kt
    @12
    @13
    @20
    hal
    hal
    hb
    vx
    ta
    @19
    @11
    @20
    ax-hbl1
    hal
    hal
    vx
    @3
    @19
    @13
    @20
    ax-17
    hbc
    exlimd.3
    hbov
    hbov
    hb
    hb
    hb
    tr
    @18
    tim
    hal
    vx
    tv
    #
    @3
    ke
    kbr
    #
    @5
    wim
    @16
    hb
    hb
    hb
    ta
    tt
    tim
    wim
    @11
    @9
    wov
    hb
    hb
    hb
    ta
    tt
    @4
    tim
    @23
    wim
    @11
    @9
    hb
    ta
    @0
    @22
    kc
    #
    @4
    @23
    @11
    ta
    @24
    ke
    kbr
    @23
    hal
    @22
    @3
    hal
    vx
    wv
    #
    @13
    weqi
    #
    hb
    @24
    ta
    kt
    hal
    hb
    @0
    @22
    @12
    @25
    wc
    hal
    hb
    vx
    ta
    @11
    beta
    eqcomi
    a1i
    hal
    hb
    @22
    @3
    @0
    @23
    @12
    @25
    @23
    @26
    id
    ceq2
    eqtri
    oveq1
    oveq2
    insti
    a1i
    mpd
    alrimiv
    hal
    hb
    ht
    #
    hb
    tex
    @0
    hal
    wex
    @12
    wc
    #
    adantr
    #
    @2
    tal
    hb
    vy
    tal
    hal
    vz
    @4
    hb
    vy
    tv
    #
    tim
    kbr
    #
    kl
    #
    kc
    #
    @30
    tim
    kbr
    #
    kl
    kc
    #
    @7
    tt
    tim
    kbr
    #
    @1
    @35
    @2
    tr
    @1
    @16
    @28
    simpr
    @1
    @35
    ke
    kbr
    @2
    @7
    @2
    @29
    ax-cb1
    hal
    vz
    vy
    @0
    @12
    exval
    a1i
    mpbi
    hb
    vy
    @34
    tt
    @36
    hb
    hb
    hb
    @33
    @30
    tim
    wim
    @27
    hb
    tal
    @32
    hal
    wal
    #
    hal
    hb
    vz
    @31
    hb
    hb
    hb
    @4
    @30
    tim
    wim
    @14
    hb
    vy
    wv
    #
    wov
    #
    wl
    #
    wc
    #
    @38
    wov
    @9
    hb
    hb
    hb
    @33
    @30
    @7
    tim
    @30
    tt
    ke
    kbr
    #
    tt
    wim
    @41
    @38
    @27
    hb
    @32
    @6
    tal
    @42
    @37
    @40
    hal
    hb
    vz
    @31
    @5
    @42
    @39
    hb
    hb
    hb
    @4
    @30
    tim
    @42
    tt
    wim
    @14
    @38
    @42
    hb
    @30
    tt
    @38
    @9
    weqi
    id
    #
    oveq2
    leq
    ceq2
    @43
    oveq12
    cla4v
    syl
    mpd
end
