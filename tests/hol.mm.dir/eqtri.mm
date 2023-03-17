include "ke.mm"
include "weq.mm"
include "eqtypi.mm"
include "kc.mm"
include "dfov1.mm"
include "hb.mm"
include "ht.mm"
include "wc.mm"
include "ceq2.mm"
include "mpbi.mm"
include "dfov2.mm"

theorem eqtri
  let hal: type al
  let ta: term A
  let tb: term B
  let tc: term C
  let tr: term R
  assume eqtri.1: |- A : al
  assume eqtri.2: |- R |= [ A = B ]
  assume eqtri.3: |- R |= [ B = C ]


  assert |- R |= [ A = C ]

  proof
    hal
    hal
    ta
    tc
    ke
    tr
    hal
    weq
    #
    eqtri.1
    hal
    tb
    tc
    tr
    hal
    ta
    tb
    tr
    eqtri.1
    eqtri.2
    eqtypi
    #
    eqtri.3
    eqtypi
    ke
    ta
    kc
    #
    tb
    kc
    @2
    tc
    kc
    tr
    hal
    hal
    ta
    tb
    ke
    tr
    @0
    eqtri.1
    @1
    eqtri.2
    dfov1
    hal
    hb
    tb
    tc
    @2
    tr
    hal
    hal
    hb
    ht
    ke
    ta
    @0
    eqtri.1
    wc
    @1
    eqtri.3
    ceq2
    mpbi
    dfov2
end
