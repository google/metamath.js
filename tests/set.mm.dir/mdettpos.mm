include "ccrg.mm"
include "wcel.mm"
include "wa.mm"
include "csymg.mm"
include "cfv.mm"
include "cbs.mm"
include "cv.mm"
include "czrh.mm"
include "cpsgn.mm"
include "ccom.mm"
include "cmgp.mm"
include "ctpos.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmulr.mm"
include "ovtpos.mm"
include "mpteq2i.mm"
include "oveq2i.mm"
include "wceq.mm"
include "mattposcl.mm"
include "adantl.mm"
include "eqid.mm"
include "mdetleib.mm"
include "syl.mm"
include "mdetleib2.mm"
include "3eqtr4a.mm"

theorem mdettpos
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cM: class M
  let cN: class N
  let vp: setvar p
  let vx: setvar x
  assume mdettpos.d: |- D = ( N maDet R )
  assume mdettpos.a: |- A = ( N Mat R )
  assume mdettpos.b: |- B = ( Base ` A )


  assert |- ( ( R e. CRing /\ M e. B ) -> ( D ` tpos M ) = ( D ` M ) )

  proof
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    wa
    #
    cR
    vp
    cN
    csymg
    cfv
    cbs
    cfv
    #
    vp
    cv
    #
    cR
    czrh
    cfv
    #
    cN
    cpsgn
    cfv
    #
    ccom
    cfv
    #
    cR
    cmgp
    cfv
    #
    vx
    cN
    vx
    cv
    #
    @4
    cfv
    #
    @9
    cM
    ctpos
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cR
    vp
    @3
    @7
    @8
    vx
    cN
    @9
    @10
    cM
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @15
    co
    #
    cmpt
    #
    cgsu
    co
    @11
    cD
    cfv
    #
    cM
    cD
    cfv
    @17
    @23
    cR
    cgsu
    vp
    @3
    @16
    @22
    @14
    @21
    @7
    @15
    @13
    @20
    @8
    cgsu
    vx
    cN
    @12
    @19
    @10
    @9
    cM
    ovtpos
    mpteq2i
    oveq2i
    oveq2i
    mpteq2i
    oveq2i
    @2
    @11
    cB
    wcel
    #
    @24
    @18
    wceq
    @1
    @25
    @0
    cA
    cB
    cR
    cM
    cN
    mdettpos.a
    mdettpos.b
    mattposcl
    adantl
    vx
    cA
    cB
    cD
    @3
    cR
    @6
    @15
    @8
    @11
    cN
    @5
    vp
    mdettpos.d
    mdettpos.a
    mdettpos.b
    @3
    eqid
    #
    @5
    eqid
    #
    @6
    eqid
    #
    @15
    eqid
    #
    @8
    eqid
    #
    mdetleib
    syl
    vx
    cA
    cB
    cD
    @3
    cR
    @6
    @15
    @8
    cM
    cN
    @5
    vp
    mdettpos.d
    mdettpos.a
    mdettpos.b
    @26
    @27
    @28
    @29
    @30
    mdetleib2
    3eqtr4a
end
