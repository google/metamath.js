include "co.mm"
include "wceq.mm"
include "wo.mm"
include "drngmul0or.mm"
include "wne.mm"
include "wb.mm"
include "wn.mm"
include "df-ne.mm"
include "orel2.mm"
include "orc.mm"
include "impbid1.mm"
include "sylbi.mm"
include "syl.mm"
include "bitrd.mm"

theorem drngmuleq0
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume drngmuleq0.b: |- B = ( Base ` R )
  assume drngmuleq0.o: |- .0. = ( 0g ` R )
  assume drngmuleq0.t: |- .x. = ( .r ` R )
  assume drngmuleq0.r: |- ( ph -> R e. DivRing )
  assume drngmuleq0.x: |- ( ph -> X e. B )
  assume drngmuleq0.y: |- ( ph -> Y e. B )
  assume drngmuleq0.e: |- ( ph -> Y =/= .0. )


  assert |- ( ph -> ( ( X .x. Y ) = .0. <-> X = .0. ) )

  proof
    wph
    cX
    cY
    c.x
    co
    c.0
    wceq
    cX
    c.0
    wceq
    #
    cY
    c.0
    wceq
    #
    wo
    #
    @0
    wph
    cB
    cR
    c.x
    cX
    cY
    c.0
    drngmuleq0.b
    drngmuleq0.o
    drngmuleq0.t
    drngmuleq0.r
    drngmuleq0.x
    drngmuleq0.y
    drngmul0or
    wph
    cY
    c.0
    wne
    #
    @2
    @0
    wb
    #
    drngmuleq0.e
    @3
    @1
    wn
    #
    @4
    cY
    c.0
    df-ne
    @5
    @2
    @0
    @1
    @0
    orel2
    @0
    @1
    orc
    impbid1
    sylbi
    syl
    bitrd
end
