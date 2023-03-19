include "coml.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cmtcomlemN.mm"
include "wi.mm"
include "3com23.mm"
include "impbid.mm"

theorem cmtcomN
  let cB: class B
  let cC: class C
  let cK: class K
  let cX: class X
  let cY: class Y
  assume cmtcom.b: |- B = ( Base ` K )
  assume cmtcom.c: |- C = ( cm ` K )


  assert |- ( ( K e. OML /\ X e. B /\ Y e. B ) -> ( X C Y <-> Y C X ) )

  proof
    cK
    coml
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    cX
    cY
    cC
    wbr
    #
    cY
    cX
    cC
    wbr
    #
    cB
    cC
    cK
    cX
    cY
    cmtcom.b
    cmtcom.c
    cmtcomlemN
    @0
    @2
    @1
    @4
    @3
    wi
    cB
    cC
    cK
    cY
    cX
    cmtcom.b
    cmtcom.c
    cmtcomlemN
    3com23
    impbid
end
