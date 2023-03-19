include "kt.mm"
include "tal.mm"
include "hb.mm"
include "ht.mm"
include "tv.mm"
include "kc.mm"
include "tim.mm"
include "kbr.mm"
include "kl.mm"
include "tex.mm"
include "wtru.mm"
include "wal.mm"
include "wim.mm"
include "wv.mm"
include "wc.mm"
include "wov.mm"
include "wl.mm"
include "simpl.mm"
include "ex.mm"
include "alrimiv.mm"
include "ke.mm"
include "weqi.mm"
include "id.mm"
include "ceq1.mm"
include "eqid.mm"
include "cl.mm"
include "a1i.mm"
include "eqtri.mm"
include "oveq2.mm"
include "leq.mm"
include "ceq2.mm"
include "cla4ev.mm"
include "syl.mm"

theorem axpow
  param hal: type al
  param vx: var x
  param vy: var y
  param vz: var z
  param ta: term A
  let vp: var p
  assume axpow.1: |- A : ( al -> bool )

  disjoint x y
  disjoint A y
  disjoint y z
  disjoint al y
  disjoint al z
  disjoint p y
  disjoint p z
  disjoint al p
  assert |- T. |= ( ? \ y : ( ( al -> bool ) -> bool ) . ( ! \ z : ( al -> bool ) . [ ( ! \ x : al . [ ( z : ( al -> bool ) x : al ) ==> ( A x : al ) ] ) ==> ( y : ( ( al -> bool ) -> bool ) z : ( al -> bool ) ) ] ) )

  proof
    kt
    tal
    hal
    hb
    ht
    #
    vz
    tal
    hal
    vx
    @0
    vz
    tv
    #
    hal
    vx
    tv
    #
    kc
    #
    ta
    @2
    kc
    #
    tim
    kbr
    #
    kl
    #
    kc
    #
    kt
    tim
    kbr
    #
    kl
    #
    kc
    #
    tex
    @0
    hb
    ht
    #
    vy
    tal
    @0
    vz
    @7
    @11
    vy
    tv
    #
    @1
    kc
    #
    tim
    kbr
    #
    kl
    #
    kc
    #
    kl
    kc
    @0
    vz
    @8
    kt
    kt
    @7
    kt
    kt
    @7
    wtru
    @0
    hb
    tal
    @6
    hal
    wal
    hal
    hb
    vx
    @5
    hb
    hb
    hb
    @3
    @4
    tim
    wim
    hal
    hb
    @1
    @2
    @0
    vz
    wv
    #
    hal
    vx
    wv
    #
    wc
    hal
    hb
    ta
    @2
    axpow.1
    @18
    wc
    wov
    wl
    wc
    #
    simpl
    ex
    alrimiv
    @11
    vy
    @16
    @0
    vp
    kt
    kl
    #
    @10
    @11
    hb
    tal
    @15
    @0
    wal
    #
    @0
    hb
    vz
    @14
    hb
    hb
    hb
    @7
    @13
    tim
    wim
    @19
    @0
    hb
    @12
    @1
    @11
    vy
    wv
    #
    @17
    wc
    #
    wov
    #
    wl
    #
    wc
    @0
    hb
    vp
    kt
    wtru
    wl
    #
    @11
    hb
    @15
    @9
    tal
    @12
    @20
    ke
    kbr
    #
    @21
    @25
    @0
    hb
    vz
    @14
    @8
    @27
    @24
    hb
    hb
    hb
    @7
    @13
    tim
    @27
    kt
    wim
    @19
    @23
    hb
    @13
    @20
    @1
    kc
    #
    kt
    @27
    @23
    @0
    hb
    @1
    @12
    @27
    @20
    @22
    @17
    @27
    @11
    @12
    @20
    @22
    @26
    weqi
    #
    id
    ceq1
    @28
    kt
    ke
    kbr
    @27
    @29
    @0
    hb
    vp
    kt
    kt
    @1
    wtru
    @17
    hb
    kt
    @0
    vp
    tv
    #
    @1
    ke
    kbr
    @0
    @30
    @1
    @0
    vp
    wv
    @17
    weqi
    wtru
    eqid
    cl
    a1i
    eqtri
    oveq2
    leq
    ceq2
    cla4ev
    syl
end
