include "cfv.mm"
include "choma.mm"
include "co.mm"
include "wcel.mm"
include "cdoma.mm"
include "wceq.mm"
include "eqid.mm"
include "idahom.mm"
include "homadm.mm"
include "syl.mm"

theorem idadm
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


  assert |- ( ph -> ( domA ` ( I ` X ) ) = X )

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
    cdoma
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
    homadm
    syl
end
