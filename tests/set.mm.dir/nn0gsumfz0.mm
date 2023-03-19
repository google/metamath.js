include "cv.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cres.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "cn0.mm"
include "wral.mm"
include "cgsu.mm"
include "w3a.mm"
include "cmap.mm"
include "wrex.mm"
include "nn0gsumfz.mm"
include "simp3.mm"
include "reximi.mm"
include "syl.mm"

theorem nn0gsumfz0
  let wph: wff ph
  let cB: class B
  let vf: setvar f
  let cF: class F
  let cG: class G
  let c.0: class .0.
  let vs: setvar s
  let vx: setvar x
  assume nn0gsumfz.b: |- B = ( Base ` G )
  assume nn0gsumfz.0: |- .0. = ( 0g ` G )
  assume nn0gsumfz.g: |- ( ph -> G e. CMnd )
  assume nn0gsumfz.f: |- ( ph -> F e. ( B ^m NN0 ) )
  assume nn0gsumfz.y: |- ( ph -> F finSupp .0. )

  disjoint B f
  disjoint F f
  disjoint F s
  disjoint f s
  disjoint G f
  disjoint .0. f
  disjoint .0. s
  disjoint f ph
  disjoint ph s
  disjoint F x
  disjoint f x
  disjoint s x
  disjoint .0. x
  assert |- ( ph -> E. s e. NN0 E. f e. ( B ^m ( 0 ... s ) ) ( G gsum F ) = ( G gsum f ) )

  proof
    wph
    vf
    cv
    #
    cF
    cc0
    vs
    cv
    #
    cfz
    co
    #
    cres
    wceq
    #
    @1
    vx
    cv
    #
    clt
    wbr
    @4
    cF
    cfv
    c.0
    wceq
    wi
    vx
    cn0
    wral
    #
    cG
    cF
    cgsu
    co
    cG
    @0
    cgsu
    co
    wceq
    #
    w3a
    #
    vf
    cB
    @2
    cmap
    co
    #
    wrex
    #
    vs
    cn0
    wrex
    @6
    vf
    @8
    wrex
    #
    vs
    cn0
    wrex
    wph
    vx
    cB
    vf
    cF
    cG
    c.0
    vs
    nn0gsumfz.b
    nn0gsumfz.0
    nn0gsumfz.g
    nn0gsumfz.f
    nn0gsumfz.y
    nn0gsumfz
    @9
    @10
    vs
    cn0
    @7
    @6
    vf
    @8
    @3
    @5
    @6
    simp3
    reximi
    reximi
    syl
end
