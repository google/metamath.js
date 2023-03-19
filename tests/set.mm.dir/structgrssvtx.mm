include "structgrssvtxlem.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cedgf.mm"
include "cpr.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "opex.mm"
include "prss.mm"
include "simpl.mm"
include "sylbir.mm"
include "syl.mm"
include "basvtxval.mm"

theorem structgrssvtx
  let wph: wff ph
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume structgrssvtx.g: |- ( ph -> G Struct X )
  assume structgrssvtx.v: |- ( ph -> V e. Y )
  assume structgrssvtx.e: |- ( ph -> E e. Z )
  assume structgrssvtx.s: |- ( ph -> { <. ( Base ` ndx ) , V >. , <. ( .ef ` ndx ) , E >. } C_ G )


  assert |- ( ph -> ( Vtx ` G ) = V )

  proof
    wph
    cG
    cV
    cX
    cY
    structgrssvtx.g
    wph
    cE
    cG
    cV
    cX
    cY
    cZ
    structgrssvtx.g
    structgrssvtx.v
    structgrssvtx.e
    structgrssvtx.s
    structgrssvtxlem
    structgrssvtx.v
    wph
    cnx
    cbs
    cfv
    #
    cV
    cop
    #
    cnx
    cedgf
    cfv
    #
    cE
    cop
    #
    cpr
    cG
    wss
    #
    @1
    cG
    wcel
    #
    structgrssvtx.s
    @4
    @5
    @3
    cG
    wcel
    #
    wa
    @5
    @1
    @3
    cG
    @0
    cV
    opex
    @2
    cE
    opex
    prss
    @5
    @6
    simpl
    sylbir
    syl
    basvtxval
end
