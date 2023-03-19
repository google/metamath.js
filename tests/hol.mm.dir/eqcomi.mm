include "ke.mm"
include "weq.mm"
include "eqtypi.mm"
include "dfov1.mm"
include "eqcomx.mm"
include "dfov2.mm"

theorem eqcomi
  param hal: type al
  param ta: term A
  param tb: term B
  param tr: term R
  assume eqcomi.1: |- A : al
  assume eqcomi.2: |- R |= [ A = B ]


  assert |- R |= [ B = A ]

  proof
    hal
    hal
    tb
    ta
    ke
    tr
    hal
    weq
    #
    hal
    ta
    tb
    tr
    eqcomi.1
    eqcomi.2
    eqtypi
    #
    eqcomi.1
    hal
    ta
    tb
    tr
    eqcomi.1
    @1
    hal
    hal
    ta
    tb
    ke
    tr
    @0
    eqcomi.1
    @1
    eqcomi.2
    dfov1
    eqcomx
    dfov2
end
