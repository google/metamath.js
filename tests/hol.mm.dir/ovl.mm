include "kl.mm"
include "kbr.mm"
include "kc.mm"
include "kt.mm"
include "ht.mm"
include "wl.mm"
include "wov.mm"
include "ke.mm"
include "weq.mm"
include "wc.mm"
include "wtru.mm"
include "df-ov.mm"
include "a1i.mm"
include "dfov2.mm"
include "distrl.mm"
include "ceq1.mm"
include "eqtri.mm"
include "tv.mm"
include "wv.mm"
include "weqi.mm"
include "cl.mm"

theorem ovl
  param hal: type al
  param hbe: type be
  param hga: type ga
  param vx: var x
  param vy: var y
  param ta: term A
  param tb: term B
  param tc: term C
  param ts: term S
  param tt: term T
  assume ovl.1: |- A : ga
  assume ovl.2: |- S : al
  assume ovl.3: |- T : be
  assume ovl.4: |- [ x : al = S ] |= [ A = B ]
  assume ovl.5: |- [ y : be = T ] |= [ B = C ]

  disjoint B x
  disjoint C y
  disjoint x y
  disjoint S x
  disjoint S y
  disjoint T y
  disjoint al x
  disjoint be y
  assert |- T. |= [ [ S \ x : al . \ y : be . A T ] = C ]

  proof
    hga
    ts
    tt
    hal
    vx
    hbe
    vy
    ta
    kl
    #
    kl
    #
    kbr
    #
    hbe
    vy
    hal
    vx
    ta
    kl
    #
    ts
    kc
    #
    kl
    #
    tt
    kc
    #
    tc
    kt
    hal
    hbe
    hga
    ts
    tt
    @1
    hal
    hbe
    hga
    ht
    #
    vx
    @0
    hbe
    hga
    vy
    ta
    ovl.1
    wl
    wl
    #
    ovl.2
    ovl.3
    wov
    #
    hga
    @2
    @1
    ts
    kc
    #
    tt
    kc
    #
    @6
    kt
    @9
    hga
    hga
    @2
    @11
    ke
    kt
    hga
    weq
    @9
    hbe
    hga
    @10
    tt
    hal
    @7
    @1
    ts
    @8
    ovl.2
    wc
    #
    ovl.3
    wc
    ke
    @2
    kc
    @11
    kc
    kt
    wtru
    hal
    hbe
    hga
    ts
    tt
    @1
    @8
    ovl.2
    ovl.3
    df-ov
    a1i
    dfov2
    hbe
    hga
    tt
    @10
    kt
    @5
    @12
    ovl.3
    @10
    @5
    ke
    kbr
    kt
    wtru
    hal
    hbe
    hga
    vx
    vy
    ta
    ts
    ovl.1
    ovl.2
    distrl
    a1i
    ceq1
    eqtri
    hbe
    hga
    vy
    @4
    tc
    tt
    hal
    hga
    @3
    ts
    hal
    hga
    vx
    ta
    ovl.1
    wl
    ovl.2
    wc
    #
    ovl.3
    hga
    @4
    tb
    tc
    hbe
    vy
    tv
    #
    tt
    ke
    kbr
    #
    @13
    @4
    tb
    ke
    kbr
    @15
    hbe
    @14
    tt
    hbe
    vy
    wv
    ovl.3
    weqi
    hal
    hga
    vx
    ta
    tb
    ts
    ovl.1
    ovl.2
    ovl.4
    cl
    a1i
    ovl.5
    eqtri
    cl
    eqtri
end
