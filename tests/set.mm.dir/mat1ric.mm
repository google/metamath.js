include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "crs.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "cric.mm"
include "wbr.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cv.mm"
include "csn.mm"
include "cmpt.mm"
include "eqid.mm"
include "weq.mm"
include "opeq2.mm"
include "sneqd.mm"
include "cbvmptv.mm"
include "mat1rngiso.mm"
include "ne0i.mm"
include "syl.mm"
include "brric.mm"
include "sylibr.mm"

theorem mat1ric
  let cA: class A
  let cR: class R
  let cE: class E
  let cV: class V
  let vy: setvar y
  let vx: setvar x
  assume mat1ric.a: |- A = ( { E } Mat R )


  assert |- ( ( R e. Ring /\ E e. V ) -> R ~=r A )

  proof
    cR
    crg
    wcel
    cE
    cV
    wcel
    wa
    #
    cR
    cA
    crs
    co
    #
    c0
    wne
    #
    cR
    cA
    cric
    wbr
    @0
    vx
    cR
    cbs
    cfv
    #
    cE
    cE
    cop
    #
    vx
    cv
    #
    cop
    #
    csn
    #
    cmpt
    #
    @1
    wcel
    @2
    vy
    cA
    cA
    cbs
    cfv
    #
    cR
    cE
    @8
    @3
    @4
    cV
    @3
    eqid
    mat1ric.a
    @9
    eqid
    @4
    eqid
    vx
    vy
    @3
    @7
    @4
    vy
    cv
    #
    cop
    #
    csn
    vx
    vy
    weq
    @6
    @11
    @5
    @10
    @4
    opeq2
    sneqd
    cbvmptv
    mat1rngiso
    @1
    @8
    ne0i
    syl
    cR
    cA
    brric
    sylibr
end
