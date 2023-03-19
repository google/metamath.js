include "tex.mm"
include "kc.mm"
include "kct.mm"
include "tal.mm"
include "tv.mm"
include "tim.mm"
include "kbr.mm"
include "kl.mm"
include "ax-cb2.mm"
include "ex.mm"
include "alrimiv.mm"
include "hb.mm"
include "ht.mm"
include "wex.mm"
include "wc.mm"
include "adantr.mm"
include "ax-cb1.mm"
include "wctl.mm"
include "simpr.mm"
include "ke.mm"
include "wct.mm"
include "exval.mm"
include "a1i.mm"
include "mpbi.mm"
include "wim.mm"
include "wal.mm"
include "wv.mm"
include "wov.mm"
include "wl.mm"
include "weqi.mm"
include "id.mm"
include "oveq2.mm"
include "leq.mm"
include "ceq2.mm"
include "oveq12.mm"
include "cla4v.mm"
include "syl.mm"
include "mpd.mm"

theorem exlimdv2
  param hal: type al
  param vx: var x
  param tf: term F
  param tr: term R
  param tt: term T
  let vp: var p
  assume exlimdv2.1: |- F : ( al -> bool )
  assume exlimdv2.2: |- ( R , ( F x : al ) ) |= T

  disjoint F x
  disjoint R x
  disjoint T x
  disjoint al x
  disjoint p x
  disjoint F p
  disjoint T p
  disjoint al p
  assert |- ( R , ( ? F ) ) |= T

  proof
    tr
    tex
    tf
    kc
    #
    kct
    #
    tal
    hal
    vx
    tf
    hal
    vx
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
    @3
    kct
    #
    exlimdv2.2
    ax-cb2
    #
    tr
    @0
    @6
    hal
    vx
    @4
    tr
    tr
    @3
    tt
    exlimdv2.2
    ex
    alrimiv
    hal
    hb
    ht
    #
    hb
    tex
    tf
    hal
    wex
    exlimdv2.1
    wc
    #
    adantr
    @1
    tal
    hb
    vp
    tal
    hal
    vx
    @3
    hb
    vp
    tv
    #
    tim
    kbr
    #
    kl
    #
    kc
    #
    @11
    tim
    kbr
    #
    kl
    kc
    #
    @6
    tt
    tim
    kbr
    #
    @0
    @16
    @1
    tr
    @0
    tr
    @3
    tt
    @7
    exlimdv2.2
    ax-cb1
    wctl
    #
    @10
    simpr
    @0
    @16
    ke
    kbr
    @1
    tr
    @0
    @18
    @10
    wct
    hal
    vx
    vp
    tf
    exlimdv2.1
    exval
    a1i
    mpbi
    hb
    vp
    @15
    tt
    @17
    hb
    hb
    hb
    @14
    @11
    tim
    wim
    @9
    hb
    tal
    @13
    hal
    wal
    #
    hal
    hb
    vx
    @12
    hb
    hb
    hb
    @3
    @11
    tim
    wim
    hal
    hb
    tf
    @2
    exlimdv2.1
    hal
    vx
    wv
    wc
    #
    hb
    vp
    wv
    #
    wov
    #
    wl
    #
    wc
    #
    @21
    wov
    @8
    hb
    hb
    hb
    @14
    @11
    @6
    tim
    @11
    tt
    ke
    kbr
    #
    tt
    wim
    @24
    @21
    @9
    hb
    @13
    @5
    tal
    @25
    @19
    @23
    hal
    hb
    vx
    @12
    @4
    @25
    @22
    hb
    hb
    hb
    @3
    @11
    tim
    @25
    tt
    wim
    @20
    @21
    @25
    hb
    @11
    tt
    @21
    @8
    weqi
    id
    #
    oveq2
    leq
    ceq2
    @26
    oveq12
    cla4v
    syl
    mpd
end
