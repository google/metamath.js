include "ciedg.mm"
include "cfv.mm"
include "cedgf.mm"
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
include "funiedgdmge2valOLD.mm"
include "syl3anc.mm"
include "edgfndxid.mm"
include "cop.mm"
include "funopfv.mm"
include "sylc.mm"
include "3eqtrd.mm"

theorem edgfiedgvalOLD
  let wph: wff ph
  let cE: class E
  let cG: class G
  let cX: class X
  let cY: class Y
  assume basvtxvalOLD.g: |- ( ph -> G e. X )
  assume basvtxvalOLD.f: |- ( ph -> Fun G )
  assume basvtxvalOLD.v: |- ( ph -> 2 <_ ( # ` dom G ) )
  assume edgfiedgvalOLD.e: |- ( ph -> E e. Y )
  assume edgfiedgvalOLD.s: |- ( ph -> <. ( .ef ` ndx ) , E >. e. G )


  assert |- ( ph -> ( iEdg ` G ) = E )

  proof
    wph
    cG
    ciedg
    cfv
    #
    cG
    cedgf
    cfv
    #
    cnx
    cedgf
    cfv
    #
    cG
    cfv
    #
    cE
    wph
    cG
    cX
    wcel
    #
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
    @6
    basvtxvalOLD.f
    @5
    cG
    fundif
    syl
    basvtxvalOLD.v
    cG
    cX
    funiedgdmge2valOLD
    syl3anc
    wph
    @4
    @1
    @3
    wceq
    basvtxvalOLD.g
    cG
    cX
    edgfndxid
    syl
    wph
    @7
    @2
    cE
    cop
    cG
    wcel
    @3
    cE
    wceq
    basvtxvalOLD.f
    edgfiedgvalOLD.s
    @2
    cE
    cG
    funopfv
    sylc
    3eqtrd
end
