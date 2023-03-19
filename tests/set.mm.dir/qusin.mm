include "cv.mm"
include "cec.mm"
include "cmpt.mm"
include "cimas.mm"
include "co.mm"
include "cxp.mm"
include "cin.mm"
include "cqus.mm"
include "cima.mm"
include "wss.mm"
include "wcel.mm"
include "wceq.mm"
include "ecinxp.mm"
include "sylan.mm"
include "mpteq2dva.mm"
include "oveq1d.mm"
include "eqid.mm"
include "qusval.mm"
include "cvv.mm"
include "eqidd.mm"
include "inex1g.mm"
include "syl.mm"
include "3eqtr4d.mm"

theorem qusin
  let wph: wff ph
  let c.sm: class .~
  let cR: class R
  let cU: class U
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vx: setvar x
  assume qusin.u: |- ( ph -> U = ( R /s .~ ) )
  assume qusin.v: |- ( ph -> V = ( Base ` R ) )
  assume qusin.e: |- ( ph -> .~ e. W )
  assume qusin.r: |- ( ph -> R e. Z )
  assume qusin.s: |- ( ph -> ( .~ " V ) C_ V )


  assert |- ( ph -> U = ( R /s ( .~ i^i ( V X. V ) ) ) )

  proof
    wph
    vx
    cV
    vx
    cv
    #
    c.sm
    cec
    #
    cmpt
    #
    cR
    cimas
    co
    vx
    cV
    @0
    c.sm
    cV
    cV
    cxp
    #
    cin
    #
    cec
    #
    cmpt
    #
    cR
    cimas
    co
    cU
    cR
    @4
    cqus
    co
    #
    wph
    @2
    @6
    cR
    cimas
    wph
    vx
    cV
    @1
    @5
    wph
    c.sm
    cV
    cima
    cV
    wss
    @0
    cV
    wcel
    @1
    @5
    wceq
    qusin.s
    cV
    @0
    c.sm
    ecinxp
    sylan
    mpteq2dva
    oveq1d
    wph
    vx
    c.sm
    cR
    cU
    @2
    cV
    cW
    cZ
    qusin.u
    qusin.v
    @2
    eqid
    qusin.e
    qusin.r
    qusval
    wph
    vx
    @4
    cR
    @7
    @6
    cV
    cvv
    cZ
    wph
    @7
    eqidd
    qusin.v
    @6
    eqid
    wph
    c.sm
    cW
    wcel
    @4
    cvv
    wcel
    qusin.e
    c.sm
    @3
    cW
    inex1g
    syl
    qusin.r
    qusval
    3eqtr4d
end
