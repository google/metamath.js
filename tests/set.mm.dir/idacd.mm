include "cfv.mm"
include "choma.mm"
include "co.mm"
include "wcel.mm"
include "ccoda.mm"
include "wceq.mm"
include "eqid.mm"
include "idahom.mm"
include "homacd.mm"
include "syl.mm"

theorem idacd
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cI: class I
  let cX: class X
  let vc: setvar c
  let vx: setvar x
  let c.1: class .1.
  let cA: class A
  assume idafval.i: |- I = ( IdA ` C )
  assume idafval.b: |- B = ( Base ` C )
  assume idafval.c: |- ( ph -> C e. Cat )
  assume idahom.x: |- ( ph -> X e. B )


  assert |- ( ph -> ( codA ` ( I ` X ) ) = X )

  proof
    wph
    cX
    cI
    cfv
    #
    cX
    cX
    cC
    choma
    cfv
    #
    co
    wcel
    @0
    ccoda
    cfv
    cX
    wceq
    wph
    cB
    cC
    @1
    cI
    cX
    idafval.i
    idafval.b
    idafval.c
    idahom.x
    @1
    eqid
    #
    idahom
    cC
    @0
    @1
    cX
    cX
    @2
    homacd
    syl
end
