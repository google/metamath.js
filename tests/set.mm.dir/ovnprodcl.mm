include "cfv.mm"
include "cr.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cn.mm"
include "ffvelrnd.mm"
include "elmapi.mm"
include "syl.mm"
include "hoiprodcl.mm"

theorem ovnprodcl
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cI: class I
  let cX: class X
  let vx: setvar x
  assume ovnprodcl.kph: |- F/ k ph
  assume ovnprodcl.x: |- ( ph -> X e. Fin )
  assume ovnprodcl.f: |- ( ph -> F : NN --> ( ( RR X. RR ) ^m X ) )
  assume ovnprodcl.i: |- ( ph -> I e. NN )

  disjoint X k
  disjoint k x
  assert |- ( ph -> prod_ k e. X ( vol ` ( ( [,) o. ( F ` I ) ) ` k ) ) e. ( 0 [,) +oo ) )

  proof
    wph
    vk
    cI
    cF
    cfv
    #
    cX
    ovnprodcl.kph
    ovnprodcl.x
    wph
    @0
    cr
    cr
    cxp
    #
    cX
    cmap
    co
    #
    wcel
    cX
    @1
    @0
    wf
    wph
    cn
    @2
    cI
    cF
    ovnprodcl.f
    ovnprodcl.i
    ffvelrnd
    @0
    @1
    cX
    elmapi
    syl
    hoiprodcl
end
