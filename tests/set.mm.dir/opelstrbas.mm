include "cbs.mm"
include "cvv.mm"
include "baseid.mm"
include "cstr.mm"
include "wbr.mm"
include "wcel.mm"
include "structex.mm"
include "syl.mm"
include "ccnv.mm"
include "wfun.mm"
include "structfung.mm"
include "strfv2d.mm"

theorem opelstrbas
  let wph: wff ph
  let cS: class S
  let cV: class V
  let cX: class X
  let cY: class Y
  assume opelstrbas.s: |- ( ph -> S Struct X )
  assume opelstrbas.v: |- ( ph -> V e. Y )
  assume opelstrbas.b: |- ( ph -> <. ( Base ` ndx ) , V >. e. S )


  assert |- ( ph -> V = ( Base ` S ) )

  proof
    wph
    cV
    cS
    cbs
    cvv
    cY
    baseid
    wph
    cS
    cX
    cstr
    wbr
    #
    cS
    cvv
    wcel
    opelstrbas.s
    cS
    cX
    structex
    syl
    wph
    @0
    cS
    ccnv
    ccnv
    wfun
    opelstrbas.s
    cS
    cX
    structfung
    syl
    opelstrbas.b
    opelstrbas.v
    strfv2d
end
