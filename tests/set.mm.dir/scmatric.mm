include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "crg.mm"
include "w3a.mm"
include "crs.mm"
include "co.mm"
include "cric.mm"
include "wbr.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cur.mm"
include "cvsca.mm"
include "cmpt.mm"
include "eqid.mm"
include "scmatrngiso.mm"
include "ne0i.mm"
include "syl.mm"
include "brric.mm"
include "sylibr.mm"

theorem scmatric
  let cA: class A
  let cC: class C
  let cR: class R
  let cS: class S
  let cN: class N
  let vx: setvar x
  assume scmatric.a: |- A = ( N Mat R )
  assume scmatric.c: |- C = ( N ScMat R )
  assume scmatric.s: |- S = ( A |`s C )


  assert |- ( ( N e. Fin /\ N =/= (/) /\ R e. Ring ) -> R ~=r S )

  proof
    cN
    cfn
    wcel
    cN
    c0
    wne
    cR
    crg
    wcel
    w3a
    #
    cR
    cS
    crs
    co
    #
    c0
    wne
    #
    cR
    cS
    cric
    wbr
    @0
    vx
    cR
    cbs
    cfv
    #
    vx
    cv
    cA
    cur
    cfv
    #
    cA
    cvsca
    cfv
    #
    co
    cmpt
    #
    @1
    wcel
    @2
    vx
    cA
    cC
    cR
    cS
    @4
    @6
    @5
    @3
    cN
    @3
    eqid
    scmatric.a
    @4
    eqid
    @5
    eqid
    @6
    eqid
    scmatric.c
    scmatric.s
    scmatrngiso
    @1
    @6
    ne0i
    syl
    cR
    cS
    brric
    sylibr
end
