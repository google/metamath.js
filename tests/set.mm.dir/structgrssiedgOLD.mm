include "structgrssvtxlemOLD.mm"
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
include "simpr.mm"
include "sylbir.mm"
include "syl.mm"
include "edgfiedgvalOLD.mm"

theorem structgrssiedgOLD
  let wph: wff ph
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  assume structgrssvtxOLD.g: |- ( ph -> G e. X )
  assume structgrssvtxOLD.f: |- ( ph -> Fun G )
  assume structgrssvtxOLD.v: |- ( ph -> V e. Y )
  assume structgrssvtxOLD.e: |- ( ph -> E e. Z )
  assume structgrssvtxOLD.s: |- ( ph -> { <. ( Base ` ndx ) , V >. , <. ( .ef ` ndx ) , E >. } C_ G )


  assert |- ( ph -> ( iEdg ` G ) = E )

  proof
    wph
    cE
    cG
    cX
    cZ
    structgrssvtxOLD.g
    structgrssvtxOLD.f
    wph
    cE
    cG
    cV
    cX
    cY
    cZ
    structgrssvtxOLD.g
    structgrssvtxOLD.f
    structgrssvtxOLD.v
    structgrssvtxOLD.e
    structgrssvtxOLD.s
    structgrssvtxlemOLD
    structgrssvtxOLD.e
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
    @3
    cG
    wcel
    #
    structgrssvtxOLD.s
    @4
    @1
    cG
    wcel
    #
    @5
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
    @6
    @5
    simpr
    sylbir
    syl
    edgfiedgvalOLD
end
