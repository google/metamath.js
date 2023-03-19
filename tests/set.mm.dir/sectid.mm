include "cfv.mm"
include "csect.mm"
include "co.mm"
include "wbr.mm"
include "cop.mm"
include "cco.mm"
include "wceq.mm"
include "chom.mm"
include "eqid.mm"
include "catidcl.mm"
include "catlid.mm"
include "issect2.mm"
include "mpbird.mm"

theorem sectid
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cI: class I
  let cX: class X
  assume invid.b: |- B = ( Base ` C )
  assume invid.i: |- I = ( Id ` C )
  assume invid.c: |- ( ph -> C e. Cat )
  assume invid.x: |- ( ph -> X e. B )


  assert |- ( ph -> ( I ` X ) ( X ( Sect ` C ) X ) ( I ` X ) )

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
    csect
    cfv
    #
    co
    wbr
    @0
    @0
    cX
    cX
    cop
    cX
    cC
    cco
    cfv
    #
    co
    co
    @0
    wceq
    wph
    cB
    cC
    @2
    cI
    @0
    cC
    chom
    cfv
    #
    cX
    cX
    invid.b
    @3
    eqid
    #
    invid.i
    invid.c
    invid.x
    @2
    eqid
    #
    invid.x
    wph
    cB
    cC
    cI
    @3
    cX
    invid.b
    @4
    invid.i
    invid.c
    invid.x
    catidcl
    #
    catlid
    wph
    cB
    cC
    @1
    @2
    cI
    @0
    @0
    @3
    cX
    cX
    invid.b
    @4
    @5
    invid.i
    @1
    eqid
    invid.c
    invid.x
    invid.x
    @6
    @6
    issect2
    mpbird
end
