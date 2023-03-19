include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "clmod.mm"
include "w3a.mm"
include "cvsca.mm"
include "cfv.mm"
include "csca.mm"
include "cbs.mm"
include "eqid.mm"
include "lmhmlmod1.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "wceq.mm"
include "resssca.mm"
include "3ad2ant3.mm"
include "lmhmsca.mm"
include "eqtrd.mm"
include "cghm.mm"
include "csubg.mm"
include "lmghm.mm"
include "lsssubg.mm"
include "3adant1.mm"
include "resghm2.mm"
include "syl2anc.mm"
include "cv.mm"
include "wa.mm"
include "lmhmlin.mm"
include "3expb.mm"
include "3ad2antl1.mm"
include "simpl3.mm"
include "ressvsca.mm"
include "oveqd.mm"
include "syl.mm"
include "eqtr4d.mm"
include "islmhmd.mm"

theorem reslmhm2
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cL: class L
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume reslmhm2.u: |- U = ( T |`s X )
  assume reslmhm2.l: |- L = ( LSubSp ` T )


  assert |- ( ( F e. ( S LMHom U ) /\ T e. LMod /\ X e. L ) -> F e. ( S LMHom T ) )

  proof
    cF
    cS
    cU
    clmhm
    co
    wcel
    #
    cT
    clmod
    wcel
    #
    cX
    cL
    wcel
    #
    w3a
    #
    vx
    vy
    cS
    cT
    cS
    cvsca
    cfv
    #
    cT
    cvsca
    cfv
    #
    cF
    cT
    csca
    cfv
    #
    cS
    csca
    cfv
    #
    @7
    cbs
    cfv
    #
    cS
    cbs
    cfv
    #
    @9
    eqid
    #
    @4
    eqid
    #
    @5
    eqid
    #
    @7
    eqid
    #
    @6
    eqid
    #
    @8
    eqid
    #
    @0
    @1
    cS
    clmod
    wcel
    @2
    cS
    cU
    cF
    lmhmlmod1
    3ad2ant1
    @0
    @1
    @2
    simp2
    @3
    @6
    cU
    csca
    cfv
    #
    @7
    @2
    @0
    @6
    @16
    wceq
    @1
    cX
    @6
    cT
    cU
    cL
    reslmhm2.u
    @14
    resssca
    3ad2ant3
    @0
    @1
    @16
    @7
    wceq
    @2
    cS
    cU
    cF
    @7
    @16
    @13
    @16
    eqid
    lmhmsca
    3ad2ant1
    eqtrd
    @3
    cF
    cS
    cU
    cghm
    co
    wcel
    #
    cX
    cT
    csubg
    cfv
    wcel
    #
    cF
    cS
    cT
    cghm
    co
    wcel
    @0
    @1
    @17
    @2
    cS
    cU
    cF
    lmghm
    3ad2ant1
    @1
    @2
    @18
    @0
    cL
    cX
    cT
    reslmhm2.l
    lsssubg
    3adant1
    cS
    cT
    cU
    cF
    cX
    reslmhm2.u
    resghm2
    syl2anc
    @3
    vx
    cv
    #
    @8
    wcel
    #
    vy
    cv
    #
    @9
    wcel
    #
    wa
    #
    wa
    #
    @19
    @21
    @4
    co
    cF
    cfv
    #
    @19
    @21
    cF
    cfv
    #
    cU
    cvsca
    cfv
    #
    co
    #
    @19
    @26
    @5
    co
    #
    @0
    @1
    @23
    @25
    @28
    wceq
    #
    @2
    @0
    @20
    @22
    @30
    @8
    cS
    cU
    @4
    @27
    @9
    cF
    @7
    @19
    @21
    @13
    @15
    @10
    @11
    @27
    eqid
    lmhmlin
    3expb
    3ad2antl1
    @24
    @2
    @29
    @28
    wceq
    @0
    @1
    @2
    @23
    simpl3
    @2
    @5
    @27
    @19
    @26
    cX
    @5
    cT
    cU
    cL
    reslmhm2.u
    @12
    ressvsca
    oveqd
    syl
    eqtr4d
    islmhmd
end
