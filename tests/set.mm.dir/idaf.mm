include "cv.mm"
include "ccid.mm"
include "cfv.mm"
include "cotp.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "otex.mm"
include "a1i.mm"
include "eqid.mm"
include "idafval.mm"
include "choma.mm"
include "co.mm"
include "homarw.mm"
include "ccat.mm"
include "adantr.mm"
include "simpr.mm"
include "idahom.mm"
include "sseldi.mm"
include "fmpt2d.mm"

theorem idaf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cI: class I
  let vc: setvar c
  let vx: setvar x
  let c.1: class .1.
  let cX: class X
  assume idafval.i: |- I = ( IdA ` C )
  assume idafval.b: |- B = ( Base ` C )
  assume idafval.c: |- ( ph -> C e. Cat )
  assume idaf.a: |- A = ( Arrow ` C )


  assert |- ( ph -> I : B --> A )

  proof
    wph
    vx
    vx
    cB
    vx
    cv
    #
    @0
    @0
    cC
    ccid
    cfv
    #
    cfv
    #
    cotp
    #
    cA
    cI
    cvv
    @3
    cvv
    wcel
    wph
    @0
    cB
    wcel
    #
    wa
    #
    @0
    @0
    @2
    otex
    a1i
    wph
    vx
    cB
    cC
    @1
    cI
    idafval.i
    idafval.b
    idafval.c
    @1
    eqid
    idafval
    @5
    @0
    @0
    cC
    choma
    cfv
    #
    co
    cA
    @0
    cI
    cfv
    cA
    cC
    @6
    @0
    @0
    idaf.a
    @6
    eqid
    #
    homarw
    @5
    cB
    cC
    @6
    cI
    @0
    idafval.i
    idafval.b
    wph
    cC
    ccat
    wcel
    @4
    idafval.c
    adantr
    wph
    @4
    simpr
    @7
    idahom
    sseldi
    fmpt2d
end
