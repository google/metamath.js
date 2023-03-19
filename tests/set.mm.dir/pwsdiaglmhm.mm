include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "cvsca.mm"
include "cfv.mm"
include "csca.mm"
include "cbs.mm"
include "eqid.mm"
include "simpl.mm"
include "pwslmod.mm"
include "pwssca.mm"
include "eqcomd.mm"
include "cgrp.mm"
include "cghm.mm"
include "co.mm"
include "lmodgrp.mm"
include "pwsdiagghm.mm"
include "sylan.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "simplr.mm"
include "lmodvscl.mm"
include "3expb.mm"
include "adantlr.mm"
include "fvdiagfn.mm"
include "syl2anc.mm"
include "cof.mm"
include "ad2ant2l.mm"
include "oveq2d.mm"
include "simpll.mm"
include "simprl.mm"
include "pwsdiagel.mm"
include "adantrl.mm"
include "pwsvscafval.mm"
include "cvv.mm"
include "id.mm"
include "vex.mm"
include "a1i.mm"
include "ofc12.mm"
include "ad2antlr.mm"
include "3eqtrd.mm"
include "eqtr4d.mm"
include "islmhmd.mm"

theorem pwsdiaglmhm
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cF: class F
  let cI: class I
  let cW: class W
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  assume pwsdiaglmhm.y: |- Y = ( R ^s I )
  assume pwsdiaglmhm.b: |- B = ( Base ` R )
  assume pwsdiaglmhm.f: |- F = ( x e. B |-> ( I X. { x } ) )

  disjoint Y x
  disjoint R x
  disjoint I x
  disjoint B x
  disjoint W x
  disjoint Y a
  disjoint Y b
  disjoint a x
  disjoint b x
  disjoint a b
  disjoint R a
  disjoint R b
  disjoint I a
  disjoint I b
  disjoint B a
  disjoint B b
  disjoint F a
  disjoint F b
  disjoint W a
  disjoint W b
  assert |- ( ( R e. LMod /\ I e. W ) -> F e. ( R LMHom Y ) )

  proof
    cR
    clmod
    wcel
    #
    cI
    cW
    wcel
    #
    wa
    #
    va
    vb
    cR
    cY
    cR
    cvsca
    cfv
    #
    cY
    cvsca
    cfv
    #
    cF
    cY
    csca
    cfv
    #
    cR
    csca
    cfv
    #
    @6
    cbs
    cfv
    #
    cB
    pwsdiaglmhm.b
    @3
    eqid
    #
    @4
    eqid
    #
    @6
    eqid
    #
    @5
    eqid
    @7
    eqid
    #
    @0
    @1
    simpl
    cR
    cI
    cW
    cY
    pwsdiaglmhm.y
    pwslmod
    @2
    @6
    @5
    cR
    @6
    cI
    clmod
    cW
    cY
    pwsdiaglmhm.y
    @10
    pwssca
    eqcomd
    @0
    cR
    cgrp
    wcel
    @1
    cF
    cR
    cY
    cghm
    co
    wcel
    cR
    lmodgrp
    vx
    cB
    cR
    cF
    cI
    cW
    cY
    pwsdiaglmhm.y
    pwsdiaglmhm.b
    pwsdiaglmhm.f
    pwsdiagghm
    sylan
    @2
    va
    cv
    #
    @7
    wcel
    #
    vb
    cv
    #
    cB
    wcel
    #
    wa
    #
    wa
    #
    @12
    @14
    @3
    co
    #
    cF
    cfv
    #
    cI
    @18
    csn
    cxp
    #
    @12
    @14
    cF
    cfv
    #
    @4
    co
    #
    @17
    @1
    @18
    cB
    wcel
    #
    @19
    @20
    wceq
    @0
    @1
    @16
    simplr
    #
    @0
    @16
    @23
    @1
    @0
    @13
    @15
    @23
    @12
    @3
    @6
    @7
    cB
    cR
    @14
    pwsdiaglmhm.b
    @10
    @8
    @11
    lmodvscl
    3expb
    adantlr
    vx
    cB
    cF
    cI
    cW
    @18
    pwsdiaglmhm.f
    fvdiagfn
    syl2anc
    @17
    @22
    @12
    cI
    @14
    csn
    cxp
    #
    @4
    co
    cI
    @12
    csn
    cxp
    @25
    @3
    cof
    co
    #
    @20
    @17
    @21
    @25
    @12
    @4
    @1
    @15
    @21
    @25
    wceq
    @0
    @13
    vx
    cB
    cF
    cI
    cW
    @14
    pwsdiaglmhm.f
    fvdiagfn
    ad2ant2l
    oveq2d
    @17
    @12
    cY
    cbs
    cfv
    #
    cR
    @4
    @3
    @6
    cI
    @7
    clmod
    cW
    @25
    cY
    pwsdiaglmhm.y
    @27
    eqid
    #
    @8
    @9
    @10
    @11
    @0
    @1
    @16
    simpll
    @24
    @2
    @13
    @15
    simprl
    @2
    @15
    @25
    @27
    wcel
    @13
    @14
    cB
    @27
    cR
    cI
    clmod
    cW
    cY
    pwsdiaglmhm.y
    pwsdiaglmhm.b
    @28
    pwsdiagel
    adantrl
    pwsvscafval
    @1
    @26
    @20
    wceq
    @0
    @16
    @1
    cI
    @12
    @14
    @3
    cW
    cvv
    cvv
    @1
    id
    @12
    cvv
    wcel
    @1
    va
    vex
    a1i
    @14
    cvv
    wcel
    @1
    vb
    vex
    a1i
    ofc12
    ad2antlr
    3eqtrd
    eqtr4d
    islmhmd
end
