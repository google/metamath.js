include "cusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "crab.mm"
include "chash.mm"
include "cle.mm"
include "cvv.mm"
include "cmpt.mm"
include "fvex.mm"
include "dmex.mm"
include "rabex.mm"
include "a1i.mm"
include "eqid.mm"
include "eleq2w.mm"
include "cbvrabv.mm"
include "usgredgedg.mm"
include "hasheqf1od.mm"
include "usgriedgleord.mm"
include "eqbrtrrd.mm"

theorem usgredgleordALT
  let ve: setvar e
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  assume usgredgleord.v: |- V = ( Vtx ` G )
  assume usgredgleord.e: |- E = ( Edg ` G )

  disjoint E e
  disjoint N e
  disjoint E f
  disjoint E x
  disjoint e f
  disjoint e x
  disjoint f x
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint f y
  disjoint x y
  disjoint N f
  disjoint N x
  disjoint N y
  disjoint e y
  disjoint V f
  disjoint V x
  disjoint V y
  assert |- ( ( G e. USGraph /\ N e. V ) -> ( # ` { e e. E | N e. e } ) <_ ( # ` V ) )

  proof
    cG
    cusgr
    wcel
    cN
    cV
    wcel
    wa
    #
    cN
    vx
    cv
    cG
    ciedg
    cfv
    #
    cfv
    wcel
    #
    vx
    @1
    cdm
    #
    crab
    #
    chash
    cfv
    cN
    ve
    cv
    wcel
    #
    ve
    cE
    crab
    #
    chash
    cfv
    cV
    chash
    cfv
    cle
    @0
    @4
    @6
    cvv
    vy
    @4
    vy
    cv
    @1
    cfv
    cmpt
    #
    @4
    cvv
    wcel
    @0
    @2
    vx
    @3
    @1
    cG
    ciedg
    fvex
    dmex
    rabex
    a1i
    vy
    @4
    @6
    vf
    vx
    cE
    @7
    cG
    @1
    cN
    cV
    usgredgleord.e
    @1
    eqid
    #
    usgredgleord.v
    @4
    eqid
    @5
    cN
    vf
    cv
    wcel
    ve
    vf
    cE
    ve
    vf
    cN
    eleq2w
    cbvrabv
    @7
    eqid
    usgredgedg
    hasheqf1od
    vx
    @1
    cG
    cN
    cV
    usgredgleord.v
    @8
    usgriedgleord
    eqbrtrrd
end
