include "cfn.mm"
include "wcel.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cima.mm"
include "wss.mm"
include "cdm.mm"
include "cnvimass.mm"
include "eqid.mm"
include "dmmptss.mm"
include "sstri.mm"
include "ssfi.mm"
include "sylancl.mm"

theorem cnvimamptfin
  let wph: wff ph
  let cN: class N
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume cnvimamptfin.n: |- ( ph -> N e. Fin )

  disjoint N p
  assert |- ( ph -> ( `' ( p e. N |-> X ) " Y ) e. Fin )

  proof
    wph
    cN
    cfn
    wcel
    vp
    cN
    cX
    cmpt
    #
    ccnv
    cY
    cima
    #
    cN
    wss
    @1
    cfn
    wcel
    cnvimamptfin.n
    @1
    @0
    cdm
    cN
    @0
    cY
    cnvimass
    vp
    cN
    cX
    @0
    @0
    eqid
    dmmptss
    sstri
    cN
    @1
    ssfi
    sylancl
end
