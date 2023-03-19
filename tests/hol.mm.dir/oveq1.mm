include "ht.mm"
include "ke.mm"
include "kbr.mm"
include "ax-cb1.mm"
include "eqid.mm"
include "oveq123.mm"

theorem oveq1
  param hal: type al
  param hbe: type be
  param hga: type ga
  param ta: term A
  param tb: term B
  param tc: term C
  param tf: term F
  param tr: term R
  assume oveq.1: |- F : ( al -> ( be -> ga ) )
  assume oveq.2: |- A : al
  assume oveq.3: |- B : be
  assume oveq1.4: |- R |= [ A = C ]


  assert |- R |= [ [ A F B ] = [ C F B ] ]

  proof
    hal
    hbe
    hga
    ta
    tb
    tc
    tf
    tr
    tf
    tb
    oveq.1
    oveq.2
    oveq.3
    hal
    hbe
    hga
    ht
    ht
    tf
    tr
    ta
    tc
    ke
    kbr
    tr
    oveq1.4
    ax-cb1
    #
    oveq.1
    eqid
    oveq1.4
    hbe
    tb
    tr
    @0
    oveq.3
    eqid
    oveq123
end
