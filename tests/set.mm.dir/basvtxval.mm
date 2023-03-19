include "cvtx.mm"
include "cfv.mm"
include "cbs.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "c2.mm"
include "cdm.mm"
include "chash.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "cstr.mm"
include "structn0fun.mm"
include "syl.mm"
include "funvtxdmge2val.mm"
include "syl2anc.mm"
include "opelstrbas.mm"
include "eqtr4d.mm"

theorem basvtxval
  let wph: wff ph
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  assume basvtxval.s: |- ( ph -> G Struct X )
  assume basvtxval.d: |- ( ph -> 2 <_ ( # ` dom G ) )
  assume basvtxval.v: |- ( ph -> V e. Y )
  assume basvtxval.b: |- ( ph -> <. ( Base ` ndx ) , V >. e. G )


  assert |- ( ph -> ( Vtx ` G ) = V )

  proof
    wph
    cG
    cvtx
    cfv
    #
    cG
    cbs
    cfv
    #
    cV
    wph
    cG
    c0
    csn
    cdif
    wfun
    #
    c2
    cG
    cdm
    chash
    cfv
    cle
    wbr
    @0
    @1
    wceq
    wph
    cG
    cX
    cstr
    wbr
    @2
    basvtxval.s
    cG
    cX
    structn0fun
    syl
    basvtxval.d
    cG
    funvtxdmge2val
    syl2anc
    wph
    cG
    cV
    cX
    cY
    basvtxval.s
    basvtxval.v
    basvtxval.b
    opelstrbas
    eqtr4d
end
