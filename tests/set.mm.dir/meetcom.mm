include "cpo.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "cop.mm"
include "cdm.mm"
include "wa.mm"
include "meetcomALT.mm"
include "adantr.mm"

theorem meetcom
  let cB: class B
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  assume meetcom.b: |- B = ( Base ` K )
  assume meetcom.m: |- ./\ = ( meet ` K )


  assert |- ( ( ( K e. Poset /\ X e. B /\ Y e. B ) /\ ( <. X , Y >. e. dom ./\ /\ <. Y , X >. e. dom ./\ ) ) -> ( X ./\ Y ) = ( Y ./\ X ) )

  proof
    cK
    cpo
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    w3a
    cX
    cY
    c.an
    co
    cY
    cX
    c.an
    co
    wceq
    cX
    cY
    cop
    c.an
    cdm
    #
    wcel
    cY
    cX
    cop
    @0
    wcel
    wa
    cB
    cK
    c.an
    cpo
    cX
    cY
    meetcom.b
    meetcom.m
    meetcomALT
    adantr
end
