include "wcel.mm"
include "cdm.mm"
include "cword.mm"
include "cv.mm"
include "cgsu.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "wrex.mm"
include "cid.mm"
include "cdif.mm"
include "cfn.mm"
include "cbs.mm"
include "cfv.mm"
include "crab.mm"
include "wfn.mm"
include "eqid.mm"
include "psgnfn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "csubmnd.mm"
include "cmrc.mm"
include "symggen.mm"
include "cmnd.mm"
include "wss.mm"
include "cgrp.mm"
include "symggrp.mm"
include "grpmnd.mm"
include "syl.mm"
include "symgtrf.mm"
include "gsumwspan.mm"
include "sylancl.mm"
include "eqtr3d.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "ovex.mm"
include "elrnmpti.mm"
include "syl6bb.mm"

theorem psgneldm2
  let vw: setvar w
  let cD: class D
  let cP: class P
  let cT: class T
  let cG: class G
  let cN: class N
  let cV: class V
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vp: setvar p
  let cW: class W
  assume psgnval.g: |- G = ( SymGrp ` D )
  assume psgnval.t: |- T = ran ( pmTrsp ` D )
  assume psgnval.n: |- N = ( pmSgn ` D )

  disjoint G w
  disjoint N w
  disjoint P w
  disjoint T w
  disjoint D w
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint G s
  disjoint t w
  disjoint t x
  disjoint G t
  disjoint w x
  disjoint G x
  disjoint N s
  disjoint N t
  disjoint N x
  disjoint P s
  disjoint P t
  disjoint P x
  disjoint T s
  disjoint T t
  disjoint T x
  disjoint p s
  disjoint D s
  disjoint p t
  disjoint D t
  disjoint p w
  disjoint D p
  disjoint G p
  disjoint T p
  disjoint V s
  disjoint V p
  disjoint W s
  disjoint W w
  assert |- ( D e. V -> ( P e. dom N <-> E. w e. Word T P = ( G gsum w ) ) )

  proof
    cD
    cV
    wcel
    #
    cP
    cN
    cdm
    #
    wcel
    cP
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
    cP
    @4
    wceq
    vw
    @2
    wrex
    @0
    @1
    @6
    cP
    @0
    @1
    vp
    cv
    cid
    cdif
    cdm
    cfn
    wcel
    vp
    cG
    cbs
    cfv
    #
    crab
    #
    @6
    cN
    @8
    wfn
    @1
    @8
    wceq
    @7
    cD
    @8
    cG
    cN
    vp
    psgnval.g
    @7
    eqid
    #
    @8
    eqid
    psgnval.n
    psgnfn
    @8
    cN
    fndm
    ax-mp
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
    @8
    @6
    vp
    @7
    cD
    cT
    cG
    @10
    cV
    psgnval.t
    psgnval.g
    @9
    @10
    eqid
    #
    symggen
    @0
    cG
    cmnd
    wcel
    #
    cT
    @7
    wss
    @11
    @6
    wceq
    @0
    cG
    cgrp
    wcel
    @13
    cD
    cG
    cV
    psgnval.g
    symggrp
    cG
    grpmnd
    syl
    @7
    cD
    cT
    cG
    psgnval.t
    psgnval.g
    @9
    symgtrf
    vw
    @7
    cT
    @10
    cG
    @9
    @12
    gsumwspan
    sylancl
    eqtr3d
    syl5eq
    eleq2d
    vw
    @2
    @4
    cP
    @5
    @5
    eqid
    cG
    @3
    cgsu
    ovex
    elrnmpti
    syl6bb
end
