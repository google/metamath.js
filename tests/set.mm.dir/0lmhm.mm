include "clmod.mm"
include "wcel.mm"
include "wceq.mm"
include "w3a.mm"
include "cvsca.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cbs.mm"
include "eqid.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "eqcomd.mm"
include "cghm.mm"
include "co.mm"
include "cgrp.mm"
include "lmodgrp.mm"
include "0ghm.mm"
include "syl2an.mm"
include "3adant3.mm"
include "cv.mm"
include "wa.mm"
include "simpl2.mm"
include "simprl.mm"
include "simpl3.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "lmodvs0.mm"
include "syl2anc.mm"
include "c0g.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fvconst2.mm"
include "oveq2d.mm"
include "ad2antll.mm"
include "simpl1.mm"
include "simprr.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "syl.mm"
include "3eqtr4rd.mm"
include "islmhmd.mm"

theorem 0lmhm
  let cB: class B
  let cS: class S
  let cT: class T
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume 0lmhm.z: |- .0. = ( 0g ` N )
  assume 0lmhm.b: |- B = ( Base ` M )
  assume 0lmhm.s: |- S = ( Scalar ` M )
  assume 0lmhm.t: |- T = ( Scalar ` N )


  assert |- ( ( M e. LMod /\ N e. LMod /\ S = T ) -> ( B X. { .0. } ) e. ( M LMHom N ) )

  proof
    cM
    clmod
    wcel
    #
    cN
    clmod
    wcel
    #
    cS
    cT
    wceq
    #
    w3a
    #
    vx
    vy
    cM
    cN
    cM
    cvsca
    cfv
    #
    cN
    cvsca
    cfv
    #
    cB
    c.0
    csn
    cxp
    #
    cT
    cS
    cS
    cbs
    cfv
    #
    cB
    0lmhm.b
    @4
    eqid
    #
    @5
    eqid
    #
    0lmhm.s
    0lmhm.t
    @7
    eqid
    #
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @3
    cS
    cT
    @0
    @1
    @2
    simp3
    eqcomd
    @0
    @1
    @6
    cM
    cN
    cghm
    co
    wcel
    #
    @2
    @0
    cM
    cgrp
    wcel
    cN
    cgrp
    wcel
    @11
    @1
    cM
    lmodgrp
    cN
    lmodgrp
    cB
    cM
    cN
    c.0
    0lmhm.z
    0lmhm.b
    0ghm
    syl2an
    3adant3
    @3
    vx
    cv
    #
    @7
    wcel
    #
    vy
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
    c.0
    @5
    co
    #
    c.0
    @12
    @14
    @6
    cfv
    #
    @5
    co
    #
    @12
    @14
    @4
    co
    #
    @6
    cfv
    #
    @17
    @1
    @12
    cT
    cbs
    cfv
    #
    wcel
    @18
    c.0
    wceq
    @0
    @1
    @2
    @16
    simpl2
    @17
    @12
    @7
    @23
    @3
    @13
    @15
    simprl
    #
    @17
    cS
    cT
    cbs
    @0
    @1
    @2
    @16
    simpl3
    fveq2d
    eleqtrd
    @5
    cT
    @23
    cN
    @12
    c.0
    0lmhm.t
    @9
    @23
    eqid
    0lmhm.z
    lmodvs0
    syl2anc
    @15
    @20
    @18
    wceq
    @3
    @13
    @15
    @19
    c.0
    @12
    @5
    cB
    c.0
    @14
    c.0
    cN
    c0g
    cfv
    cvv
    0lmhm.z
    cN
    c0g
    fvex
    eqeltri
    #
    fvconst2
    oveq2d
    ad2antll
    @17
    @21
    cB
    wcel
    #
    @22
    c.0
    wceq
    @17
    @0
    @13
    @15
    @26
    @0
    @1
    @2
    @16
    simpl1
    @24
    @3
    @13
    @15
    simprr
    @12
    @4
    cS
    @7
    cB
    cM
    @14
    0lmhm.b
    0lmhm.s
    @8
    @10
    lmodvscl
    syl3anc
    cB
    c.0
    @21
    @25
    fvconst2
    syl
    3eqtr4rd
    islmhmd
end
