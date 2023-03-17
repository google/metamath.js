include "kc.mm"
include "kbr.mm"
include "hb.mm"
include "wov.mm"
include "ke.mm"
include "ax-cb1.mm"
include "df-ov.mm"
include "a1i.mm"
include "mpbirx.mm"

theorem dfov2
  let hal: type al
  let hbe: type be
  let ta: term A
  let tb: term B
  let tf: term F
  let tr: term R
  assume dfov1.1: |- F : ( al -> ( be -> bool ) )
  assume dfov1.2: |- A : al
  assume dfov1.3: |- B : be
  assume dfov2.4: |- R |= ( ( F A ) B )


  assert |- R |= [ A F B ]

  proof
    tf
    ta
    kc
    tb
    kc
    #
    ta
    tb
    tf
    kbr
    #
    tr
    hal
    hbe
    hb
    ta
    tb
    tf
    dfov1.1
    dfov1.2
    dfov1.3
    wov
    dfov2.4
    ke
    @1
    kc
    @0
    kc
    tr
    @0
    tr
    dfov2.4
    ax-cb1
    hal
    hbe
    hb
    ta
    tb
    tf
    dfov1.1
    dfov1.2
    dfov1.3
    df-ov
    a1i
    mpbirx
end
