include "cqus.mm"
include "co.mm"
include "cimas.mm"
include "cvv.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "cec.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-qus.mm"
include "a1i.mm"
include "wa.mm"
include "simprl.mm"
include "fveq2d.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "eceq2.mm"
include "ad2antll.mm"
include "mpteq12dv.mm"
include "syl6eqr.mm"
include "oveq12d.mm"
include "wcel.mm"
include "elex.mm"
include "syl.mm"
include "ovexd.mm"
include "ovmpt2d.mm"
include "eqtrd.mm"

theorem qusval
  let wph: wff ph
  let vx: setvar x
  let c.sm: class .~
  let cR: class R
  let cU: class U
  let cF: class F
  let cV: class V
  let cW: class W
  let cZ: class Z
  let ve: setvar e
  let vr: setvar r
  let vy: setvar y
  assume qusval.u: |- ( ph -> U = ( R /s .~ ) )
  assume qusval.v: |- ( ph -> V = ( Base ` R ) )
  assume qusval.f: |- F = ( x e. V |-> [ x ] .~ )
  assume qusval.e: |- ( ph -> .~ e. W )
  assume qusval.r: |- ( ph -> R e. Z )

  disjoint .~ x
  disjoint ph x
  disjoint R x
  disjoint V x
  disjoint e r
  disjoint e x
  disjoint e y
  disjoint .~ e
  disjoint r x
  disjoint r y
  disjoint .~ r
  disjoint x y
  disjoint .~ y
  disjoint F e
  disjoint F r
  disjoint e ph
  disjoint ph r
  disjoint R e
  disjoint R r
  disjoint V y
  assert |- ( ph -> U = ( F "s R ) )

  proof
    wph
    cU
    cR
    c.sm
    cqus
    co
    cF
    cR
    cimas
    co
    #
    qusval.u
    wph
    vr
    ve
    cR
    c.sm
    cvv
    cvv
    vx
    vr
    cv
    #
    cbs
    cfv
    #
    vx
    cv
    #
    ve
    cv
    #
    cec
    #
    cmpt
    #
    @1
    cimas
    co
    #
    @0
    cqus
    cvv
    cqus
    vr
    ve
    cvv
    cvv
    @7
    cmpt2
    wceq
    wph
    vx
    ve
    vr
    df-qus
    a1i
    wph
    @1
    cR
    wceq
    #
    @4
    c.sm
    wceq
    #
    wa
    #
    wa
    #
    @6
    cF
    @1
    cR
    cimas
    @11
    @6
    vx
    cV
    @3
    c.sm
    cec
    #
    cmpt
    cF
    @11
    vx
    @2
    @5
    cV
    @12
    @11
    @2
    cR
    cbs
    cfv
    #
    cV
    @11
    @1
    cR
    cbs
    wph
    @8
    @9
    simprl
    #
    fveq2d
    wph
    cV
    @13
    wceq
    @10
    qusval.v
    adantr
    eqtr4d
    @9
    @5
    @12
    wceq
    wph
    @8
    @4
    c.sm
    @3
    eceq2
    ad2antll
    mpteq12dv
    qusval.f
    syl6eqr
    @14
    oveq12d
    wph
    cR
    cZ
    wcel
    cR
    cvv
    wcel
    qusval.r
    cR
    cZ
    elex
    syl
    wph
    c.sm
    cW
    wcel
    c.sm
    cvv
    wcel
    qusval.e
    c.sm
    cW
    elex
    syl
    wph
    cF
    cR
    cimas
    ovexd
    ovmpt2d
    eqtrd
end
