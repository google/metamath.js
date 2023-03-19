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
  param hal: type al
  param ta: term A
  param tb: term B
  param tc: term C
  param tr: term R
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
