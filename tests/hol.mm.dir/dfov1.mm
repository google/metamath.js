include "kbr.mm"
include "kc.mm"
include "ke.mm"
include "ax-cb1.mm"
include "hb.mm"
include "df-ov.mm"
include "a1i.mm"
include "ax-eqmp.mm"

theorem dfov1
  let hal: type al
  let hbe: type be
  let ta: term A
  let tb: term B
  let tf: term F
  let tr: term R
  assume dfov1.1: |- F : ( al -> ( be -> bool ) )
  assume dfov1.2: |- A : al
  assume dfov1.3: |- B : be
  assume dfov1.4: |- R |= [ A F B ]


  assert |- R |= ( ( F A ) B )

  proof
    ta
    tb
    tf
    kbr
    #
    tf
    ta
    kc
    tb
    kc
    #
    tr
    dfov1.4
    ke
    @0
    kc
    @1
    kc
    tr
    @0
    tr
    dfov1.4
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
    ax-eqmp
end
