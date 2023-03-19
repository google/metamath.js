include "cvtx.mm"
include "cfv.mm"
include "cbs.mm"
include "cnx.mm"
include "wcel.mm"
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
include "fundif.mm"
include "syl.mm"
include "funvtxdmge2valOLD.mm"
include "syl3anc.mm"
include "c1.mm"
include "df-base.mm"
include "1nn.mm"
include "strndxid.mm"
include "cop.mm"
include "funopfv.mm"
include "sylc.mm"
include "3eqtr2d.mm"

theorem basvtxvalOLD
  let wph: wff ph
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  assume basvtxvalOLD.g: |- ( ph -> G e. X )
  assume basvtxvalOLD.f: |- ( ph -> Fun G )
  assume basvtxvalOLD.v: |- ( ph -> 2 <_ ( # ` dom G ) )
  assume basvtxvalOLD.e: |- ( ph -> V e. Y )
  assume basvtxvalOLD.s: |- ( ph -> <. ( Base ` ndx ) , V >. e. G )


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
    cnx
    cbs
    cfv
    #
    cG
    cfv
    #
    cV
    wph
    cG
    cX
    wcel
    cG
    c0
    csn
    #
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
    basvtxvalOLD.g
    wph
    cG
    wfun
    #
    @5
    basvtxvalOLD.f
    @4
    cG
    fundif
    syl
    basvtxvalOLD.v
    cG
    cX
    funvtxdmge2valOLD
    syl3anc
    wph
    cG
    cbs
    c1
    cX
    basvtxvalOLD.g
    df-base
    1nn
    strndxid
    wph
    @6
    @2
    cV
    cop
    cG
    wcel
    @3
    cV
    wceq
    basvtxvalOLD.f
    basvtxvalOLD.s
    @2
    cV
    cG
    funopfv
    sylc
    3eqtr2d
end
