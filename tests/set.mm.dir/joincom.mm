include "cpo.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "cop.mm"
include "cdm.mm"
include "wa.mm"
include "joincomALT.mm"
include "adantr.mm"

theorem joincom
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let cX: class X
  let cY: class Y
  assume joincom.b: |- B = ( Base ` K )
  assume joincom.j: |- .\/ = ( join ` K )


  assert |- ( ( ( K e. Poset /\ X e. B /\ Y e. B ) /\ ( <. X , Y >. e. dom .\/ /\ <. Y , X >. e. dom .\/ ) ) -> ( X .\/ Y ) = ( Y .\/ X ) )

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
    c.or
    co
    cY
    cX
    c.or
    co
    wceq
    cX
    cY
    cop
    c.or
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
    c.or
    cK
    cpo
    cX
    cY
    joincom.b
    joincom.j
    joincomALT
    adantr
end
