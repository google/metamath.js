include "cfv.mm"
include "cinv.mm"
include "co.mm"
include "wbr.mm"
include "csect.mm"
include "sectid.mm"
include "eqid.mm"
include "isinv.mm"
include "mpbir2and.mm"

theorem invid
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cI: class I
  let cX: class X
  assume invid.b: |- B = ( Base ` C )
  assume invid.i: |- I = ( Id ` C )
  assume invid.c: |- ( ph -> C e. Cat )
  assume invid.x: |- ( ph -> X e. B )


  assert |- ( ph -> ( I ` X ) ( X ( Inv ` C ) X ) ( I ` X ) )

  proof
    wph
    cX
    cI
    cfv
    #
    @0
    cX
    cX
    cC
    cinv
    cfv
    #
    co
    wbr
    @0
    @0
    cX
    cX
    cC
    csect
    cfv
    #
    co
    wbr
    #
    @3
    wph
    cB
    cC
    cI
    cX
    invid.b
    invid.i
    invid.c
    invid.x
    sectid
    #
    @4
    wph
    cB
    cC
    @2
    @0
    @0
    @1
    cX
    cX
    invid.b
    @1
    eqid
    invid.c
    invid.x
    invid.x
    @2
    eqid
    isinv
    mpbir2and
end
