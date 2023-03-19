include "cfv.mm"
include "ccid.mm"
include "cotp.mm"
include "co.mm"
include "eqid.mm"
include "idaval.mm"
include "chom.mm"
include "catidcl.mm"
include "elhomai2.mm"
include "eqeltrd.mm"

theorem idahom
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cH: class H
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
  assume idahom.h: |- H = ( HomA ` C )


  assert |- ( ph -> ( I ` X ) e. ( X H X ) )

  proof
    wph
    cX
    cI
    cfv
    cX
    cX
    cX
    cC
    ccid
    cfv
    #
    cfv
    #
    cotp
    cX
    cX
    cH
    co
    wph
    cB
    cC
    @0
    cI
    cX
    idafval.i
    idafval.b
    idafval.c
    @0
    eqid
    #
    idahom.x
    idaval
    wph
    cB
    cC
    @1
    cH
    cC
    chom
    cfv
    #
    cX
    cX
    idahom.h
    idafval.b
    idafval.c
    @3
    eqid
    #
    idahom.x
    idahom.x
    wph
    cB
    cC
    @0
    @3
    cX
    idafval.b
    @4
    @2
    idafval.c
    idahom.x
    catidcl
    elhomai2
    eqeltrd
end
