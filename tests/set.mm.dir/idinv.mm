include "cinv.mm"
include "cfv.mm"
include "co.mm"
include "wfun.mm"
include "wbr.mm"
include "wceq.mm"
include "eqid.mm"
include "invfun.mm"
include "invid.mm"
include "funbrfv.mm"
include "sylc.mm"

theorem idinv
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cI: class I
  let cX: class X
  assume invid.b: |- B = ( Base ` C )
  assume invid.i: |- I = ( Id ` C )
  assume invid.c: |- ( ph -> C e. Cat )
  assume invid.x: |- ( ph -> X e. B )


  assert |- ( ph -> ( ( X ( Inv ` C ) X ) ` ( I ` X ) ) = ( I ` X ) )

  proof
    wph
    cX
    cX
    cC
    cinv
    cfv
    #
    co
    #
    wfun
    cX
    cI
    cfv
    #
    @2
    @1
    wbr
    @2
    @1
    cfv
    @2
    wceq
    wph
    cB
    cC
    @0
    cX
    cX
    invid.b
    @0
    eqid
    invid.c
    invid.x
    invid.x
    invfun
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
    @2
    @2
    @1
    funbrfv
    sylc
end
