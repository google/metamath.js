include "cfv.mm"
include "ciso.mm"
include "cinv.mm"
include "eqid.mm"
include "invid.mm"
include "inviso1.mm"

theorem idiso
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cI: class I
  let cX: class X
  assume invid.b: |- B = ( Base ` C )
  assume invid.i: |- I = ( Id ` C )
  assume invid.c: |- ( ph -> C e. Cat )
  assume invid.x: |- ( ph -> X e. B )


  assert |- ( ph -> ( I ` X ) e. ( X ( Iso ` C ) X ) )

  proof
    wph
    cB
    cC
    cX
    cI
    cfv
    #
    @0
    cC
    ciso
    cfv
    #
    cC
    cinv
    cfv
    #
    cX
    cX
    invid.b
    @2
    eqid
    invid.c
    invid.x
    invid.x
    @1
    eqid
    wph
    cB
    cC
    cI
    cX
    invid.b
    invid.i
    invid.c
    invid.x
    invid
    inviso1
end
