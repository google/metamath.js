include "clmod.mm"
include "wcel.mm"
include "crn.mm"
include "wss.mm"
include "w3a.mm"
include "clmhm.mm"
include "co.mm"
include "wa.mm"
include "cvsca.mm"
include "cfv.mm"
include "csca.mm"
include "cbs.mm"
include "eqid.mm"
include "lmhmlmod1.mm"
include "adantl.mm"
include "simpl1.mm"
include "simpl2.mm"
include "lsslmod.mm"
include "syl2anc.mm"
include "wceq.mm"
include "resssca.mm"
include "3ad2ant2.mm"
include "lmhmsca.mm"
include "sylan9req.mm"
include "cghm.mm"
include "lmghm.mm"
include "csubg.mm"
include "wb.mm"
include "lsssubg.mm"
include "resghm2b.mm"
include "stoic3.mm"
include "biimpa.mm"
include "sylan2.mm"
include "cv.mm"
include "lmhmlin.mm"
include "3expb.mm"
include "adantll.mm"
include "simpll2.mm"
include "ressvsca.mm"
include "oveqd.mm"
include "syl.mm"
include "eqtrd.mm"
include "islmhmd.mm"
include "simpr.mm"
include "reslmhm2.mm"
include "syl3anc.mm"
include "impbida.mm"

theorem reslmhm2b
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


  assert |- ( ( T e. LMod /\ X e. L /\ ran F C_ X ) -> ( F e. ( S LMHom T ) <-> F e. ( S LMHom U ) ) )

  proof
    cT
    clmod
    wcel
    #
    cX
    cL
    wcel
    #
    cF
    crn
    cX
    wss
    #
    w3a
    #
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    cF
    cS
    cU
    clmhm
    co
    wcel
    #
    @3
    @4
    wa
    #
    vx
    vy
    cS
    cU
    cS
    cvsca
    cfv
    #
    cU
    cvsca
    cfv
    #
    cF
    cU
    csca
    cfv
    #
    cS
    csca
    cfv
    #
    @10
    cbs
    cfv
    #
    cS
    cbs
    cfv
    #
    @12
    eqid
    #
    @7
    eqid
    #
    @8
    eqid
    @10
    eqid
    #
    @9
    eqid
    @11
    eqid
    #
    @4
    cS
    clmod
    wcel
    @3
    cS
    cT
    cF
    lmhmlmod1
    adantl
    @6
    @0
    @1
    cU
    clmod
    wcel
    @0
    @1
    @2
    @4
    simpl1
    @0
    @1
    @2
    @4
    simpl2
    cL
    cX
    cT
    cU
    reslmhm2.u
    reslmhm2.l
    lsslmod
    syl2anc
    @3
    @4
    @9
    cT
    csca
    cfv
    #
    @10
    @1
    @0
    @17
    @9
    wceq
    @2
    cX
    @17
    cT
    cU
    cL
    reslmhm2.u
    @17
    eqid
    #
    resssca
    3ad2ant2
    cS
    cT
    cF
    @10
    @17
    @15
    @18
    lmhmsca
    sylan9req
    @4
    @3
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cF
    cS
    cU
    cghm
    co
    wcel
    #
    cS
    cT
    cF
    lmghm
    @3
    @19
    @20
    @0
    @1
    cX
    cT
    csubg
    cfv
    wcel
    @2
    @19
    @20
    wb
    cL
    cX
    cT
    reslmhm2.l
    lsssubg
    cS
    cT
    cU
    cF
    cX
    reslmhm2.u
    resghm2b
    stoic3
    biimpa
    sylan2
    @6
    vx
    cv
    #
    @11
    wcel
    #
    vy
    cv
    #
    @12
    wcel
    #
    wa
    #
    wa
    #
    @21
    @23
    @7
    co
    cF
    cfv
    #
    @21
    @23
    cF
    cfv
    #
    cT
    cvsca
    cfv
    #
    co
    #
    @21
    @28
    @8
    co
    #
    @4
    @25
    @27
    @30
    wceq
    #
    @3
    @4
    @22
    @24
    @32
    @11
    cS
    cT
    @7
    @29
    @12
    cF
    @10
    @21
    @23
    @15
    @16
    @13
    @14
    @29
    eqid
    #
    lmhmlin
    3expb
    adantll
    @26
    @1
    @30
    @31
    wceq
    @0
    @1
    @2
    @4
    @25
    simpll2
    @1
    @29
    @8
    @21
    @28
    cX
    @29
    cT
    cU
    cL
    reslmhm2.u
    @33
    ressvsca
    oveqd
    syl
    eqtrd
    islmhmd
    @3
    @5
    wa
    @5
    @0
    @1
    @4
    @3
    @5
    simpr
    @0
    @1
    @2
    @5
    simpl1
    @0
    @1
    @2
    @5
    simpl2
    cS
    cT
    cU
    cF
    cL
    cX
    reslmhm2.u
    reslmhm2.l
    reslmhm2
    syl3anc
    impbida
end
