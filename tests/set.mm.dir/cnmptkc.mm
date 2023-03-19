include "cv.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "cxko.mm"
include "co.mm"
include "ccn.mm"
include "fconstmpt.mm"
include "mpteq2i.mm"
include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "xkoccn.mm"
include "syl2anc.mm"
include "syl5eqelr.mm"

theorem cnmptkc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let cL: class L
  let cM: class M
  let vz: setvar z
  let cZ: class Z
  let cA: class A
  let cB: class B
  let cC: class C
  assume cnmptk1.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmptk1.k: |- ( ph -> K e. ( TopOn ` Y ) )

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint w x
  disjoint w y
  disjoint J w
  disjoint K w
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint w z
  disjoint Z w
  disjoint x z
  disjoint Z x
  disjoint y z
  disjoint Z y
  disjoint Z z
  disjoint A w
  disjoint A z
  disjoint B w
  disjoint B x
  disjoint ph w
  disjoint X w
  disjoint Y w
  disjoint C z
  assert |- ( ph -> ( x e. X |-> ( y e. Y |-> x ) ) e. ( J Cn ( J ^ko K ) ) )

  proof
    wph
    vx
    cX
    vy
    cY
    vx
    cv
    #
    cmpt
    #
    cmpt
    vx
    cX
    cY
    @0
    csn
    cxp
    #
    cmpt
    #
    cJ
    cJ
    cK
    cxko
    co
    ccn
    co
    #
    vx
    cX
    @2
    @1
    vy
    cY
    @0
    fconstmpt
    mpteq2i
    wph
    cK
    cY
    ctopon
    cfv
    wcel
    cJ
    cX
    ctopon
    cfv
    wcel
    @3
    @4
    wcel
    cnmptk1.k
    cnmptk1.j
    vx
    cK
    cJ
    cY
    cX
    xkoccn
    syl2anc
    syl5eqelr
end
