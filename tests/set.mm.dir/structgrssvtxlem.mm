include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cedgf.mm"
include "cvv.mm"
include "fvexd.mm"
include "cstr.mm"
include "wbr.mm"
include "wcel.mm"
include "structex.mm"
include "syl.mm"
include "wne.mm"
include "slotsbaseefdif.mm"
include "a1i.mm"
include "hashdmpropge2.mm"

theorem structgrssvtxlem
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


  assert |- ( ph -> 2 <_ ( # ` dom G ) )

  proof
    wph
    cnx
    cbs
    cfv
    #
    cnx
    cedgf
    cfv
    #
    cV
    cE
    cG
    cvv
    cvv
    cY
    cZ
    cvv
    wph
    cnx
    cbs
    fvexd
    wph
    cnx
    cedgf
    fvexd
    structgrssvtx.v
    structgrssvtx.e
    wph
    cG
    cX
    cstr
    wbr
    cG
    cvv
    wcel
    structgrssvtx.g
    cG
    cX
    structex
    syl
    @0
    @1
    wne
    wph
    slotsbaseefdif
    a1i
    structgrssvtx.s
    hashdmpropge2
end
