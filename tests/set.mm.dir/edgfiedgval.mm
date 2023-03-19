include "ciedg.mm"
include "cfv.mm"
include "cedgf.mm"
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
include "funiedgdmge2val.mm"
include "syl2anc.mm"
include "cvv.mm"
include "edgfid.mm"
include "wcel.mm"
include "structex.mm"
include "ccnv.mm"
include "structfung.mm"
include "strfv2d.mm"
include "eqtr4d.mm"

theorem edgfiedgval
  let wph: wff ph
  let cE: class E
  let cG: class G
  let cX: class X
  let cY: class Y
  assume basvtxval.s: |- ( ph -> G Struct X )
  assume basvtxval.d: |- ( ph -> 2 <_ ( # ` dom G ) )
  assume edgfiedgval.e: |- ( ph -> E e. Y )
  assume edgfiedgval.f: |- ( ph -> <. ( .ef ` ndx ) , E >. e. G )


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
    cE
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
    #
    @2
    basvtxval.s
    cG
    cX
    structn0fun
    syl
    basvtxval.d
    cG
    funiedgdmge2val
    syl2anc
    wph
    cE
    cG
    cedgf
    cvv
    cY
    edgfid
    wph
    @3
    cG
    cvv
    wcel
    basvtxval.s
    cG
    cX
    structex
    syl
    wph
    @3
    cG
    ccnv
    ccnv
    wfun
    basvtxval.s
    cG
    cX
    structfung
    syl
    edgfiedgval.f
    edgfiedgval.e
    strfv2d
    eqtr4d
end
