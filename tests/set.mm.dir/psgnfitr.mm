include "cfn.mm"
include "wcel.mm"
include "cword.mm"
include "cv.mm"
include "cgsu.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "wrex.mm"
include "csubmnd.mm"
include "cfv.mm"
include "cmrc.mm"
include "eqid.mm"
include "symggen2.mm"
include "cmnd.mm"
include "cbs.mm"
include "wss.mm"
include "cgrp.mm"
include "symggrp.mm"
include "grpmnd.mm"
include "syl.mm"
include "symgtrf.mm"
include "gsumwspan.mm"
include "sylancl.mm"
include "eqtr3d.mm"
include "eleq2d.mm"
include "ovex.mm"
include "elrnmpti.mm"
include "syl6bb.mm"

theorem psgnfitr
  let vw: setvar w
  let cB: class B
  let cQ: class Q
  let cT: class T
  let cG: class G
  let cN: class N
  assume psgnfitr.g: |- G = ( SymGrp ` N )
  assume psgnfitr.p: |- B = ( Base ` G )
  assume psgnfitr.t: |- T = ran ( pmTrsp ` N )

  disjoint G w
  disjoint Q w
  disjoint T w
  assert |- ( N e. Fin -> ( Q e. B <-> E. w e. Word T Q = ( G gsum w ) ) )

  proof
    cN
    cfn
    wcel
    #
    cQ
    cB
    wcel
    cQ
    vw
    cT
    cword
    #
    cG
    vw
    cv
    #
    cgsu
    co
    #
    cmpt
    #
    crn
    #
    wcel
    cQ
    @3
    wceq
    vw
    @1
    wrex
    @0
    cB
    @5
    cQ
    @0
    cT
    cG
    csubmnd
    cfv
    cmrc
    cfv
    #
    cfv
    #
    cB
    @5
    cB
    cN
    cT
    cG
    @6
    psgnfitr.t
    psgnfitr.g
    psgnfitr.p
    @6
    eqid
    #
    symggen2
    @0
    cG
    cmnd
    wcel
    #
    cT
    cG
    cbs
    cfv
    #
    wss
    @7
    @5
    wceq
    @0
    cG
    cgrp
    wcel
    @9
    cN
    cG
    cfn
    psgnfitr.g
    symggrp
    cG
    grpmnd
    syl
    @10
    cN
    cT
    cG
    psgnfitr.t
    psgnfitr.g
    @10
    eqid
    #
    symgtrf
    vw
    @10
    cT
    @6
    cG
    @11
    @8
    gsumwspan
    sylancl
    eqtr3d
    eleq2d
    vw
    @1
    @3
    cQ
    @4
    @4
    eqid
    cG
    @2
    cgsu
    ovex
    elrnmpti
    syl6bb
end
