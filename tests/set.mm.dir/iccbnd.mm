include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cme.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "cbnd.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "cc.mm"
include "wss.mm"
include "cnmet.mm"
include "cicc.mm"
include "iccssre.mm"
include "syl5eqss.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "metres2.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "resubcl.mm"
include "ancoms.mm"
include "oveqi.mm"
include "wceq.mm"
include "ovres.mm"
include "adantl.mm"
include "syl5eq.mm"
include "sselda.mm"
include "anim12dan.mm"
include "eqid.mm"
include "cnmetdval.mm"
include "syl.mm"
include "eqtrd.mm"
include "caddc.mm"
include "w3a.mm"
include "simprr.mm"
include "syl6eleq.mm"
include "wb.mm"
include "elicc2.mm"
include "adantr.mm"
include "mpbid.mm"
include "simp1d.mm"
include "syl2anc.mm"
include "simpll.mm"
include "simprl.mm"
include "simplr.mm"
include "simp3d.mm"
include "lesub1dd.mm"
include "subled.mm"
include "simp2d.mm"
include "letrd.mm"
include "readdcld.mm"
include "lesub2dd.mm"
include "lesubadd2d.mm"
include "absdifled.mm"
include "mpbir2and.mm"
include "eqbrtrd.mm"
include "ralrimivva.mm"
include "breq2.mm"
include "2ralbidv.mm"
include "rspcev.mm"
include "isbnd3b.mm"
include "sylanbrc.mm"

theorem iccbnd
  let cA: class A
  let cB: class B
  let cJ: class J
  let cM: class M
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume iccbnd.1: |- J = ( A [,] B )
  assume iccbnd.2: |- M = ( ( abs o. - ) |` ( J X. J ) )


  assert |- ( ( A e. RR /\ B e. RR ) -> M e. ( Bnd ` J ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cM
    cJ
    cme
    cfv
    #
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cM
    co
    #
    vr
    cv
    #
    cle
    wbr
    #
    vy
    cJ
    wral
    vx
    cJ
    wral
    #
    vr
    cr
    wrex
    #
    cM
    cJ
    cbnd
    cfv
    wcel
    @2
    cM
    cabs
    cmin
    ccom
    #
    cJ
    cJ
    cxp
    cres
    #
    @3
    iccbnd.2
    @2
    @11
    cc
    cme
    cfv
    wcel
    cJ
    cc
    wss
    @12
    @3
    wcel
    cnmet
    @2
    cJ
    cr
    cc
    @2
    cJ
    cA
    cB
    cicc
    co
    #
    cr
    iccbnd.1
    cA
    cB
    iccssre
    syl5eqss
    ax-resscn
    syl6ss
    #
    @11
    cJ
    cc
    metres2
    sylancr
    syl5eqel
    @2
    cB
    cA
    cmin
    co
    #
    cr
    wcel
    #
    @6
    @15
    cle
    wbr
    #
    vy
    cJ
    wral
    vx
    cJ
    wral
    #
    @10
    @1
    @0
    @16
    cB
    cA
    resubcl
    ancoms
    #
    @2
    @17
    vx
    vy
    cJ
    cJ
    @2
    @4
    cJ
    wcel
    #
    @5
    cJ
    wcel
    #
    wa
    #
    wa
    #
    @6
    @4
    @5
    cmin
    co
    cabs
    cfv
    #
    @15
    cle
    @23
    @6
    @4
    @5
    @11
    co
    #
    @24
    @23
    @6
    @4
    @5
    @12
    co
    #
    @25
    cM
    @12
    @4
    @5
    iccbnd.2
    oveqi
    @22
    @26
    @25
    wceq
    @2
    @4
    @5
    cJ
    cJ
    @11
    ovres
    adantl
    syl5eq
    @23
    @4
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    wa
    @25
    @24
    wceq
    @2
    @20
    @27
    @21
    @28
    @2
    cJ
    cc
    @4
    @14
    sselda
    @2
    cJ
    cc
    @5
    @14
    sselda
    anim12dan
    @4
    @5
    @11
    @11
    eqid
    cnmetdval
    syl
    eqtrd
    @23
    @24
    @15
    cle
    wbr
    @5
    @15
    cmin
    co
    #
    @4
    cle
    wbr
    @4
    @5
    @15
    caddc
    co
    #
    cle
    wbr
    @23
    @29
    cA
    @4
    @23
    @5
    cr
    wcel
    #
    @16
    @29
    cr
    wcel
    @23
    @31
    cA
    @5
    cle
    wbr
    #
    @5
    cB
    cle
    wbr
    #
    @23
    @5
    @13
    wcel
    #
    @31
    @32
    @33
    w3a
    #
    @23
    @5
    cJ
    @13
    @2
    @20
    @21
    simprr
    iccbnd.1
    syl6eleq
    @2
    @34
    @35
    wb
    @22
    cA
    cB
    @5
    elicc2
    adantr
    mpbid
    #
    simp1d
    #
    @2
    @16
    @22
    @19
    adantr
    #
    @5
    @15
    resubcl
    syl2anc
    @0
    @1
    @22
    simpll
    #
    @23
    @4
    cr
    wcel
    #
    cA
    @4
    cle
    wbr
    #
    @4
    cB
    cle
    wbr
    #
    @23
    @4
    @13
    wcel
    #
    @40
    @41
    @42
    w3a
    #
    @23
    @4
    cJ
    @13
    @2
    @20
    @21
    simprl
    iccbnd.1
    syl6eleq
    @2
    @43
    @44
    wb
    @22
    cA
    cB
    @4
    elicc2
    adantr
    mpbid
    #
    simp1d
    #
    @23
    @5
    cA
    @15
    @37
    @39
    @38
    @23
    @5
    cB
    cA
    @37
    @0
    @1
    @22
    simplr
    #
    @39
    @23
    @31
    @32
    @33
    @36
    simp3d
    lesub1dd
    subled
    @23
    @40
    @41
    @42
    @45
    simp2d
    letrd
    @23
    @4
    cB
    @30
    @46
    @47
    @23
    @5
    @15
    @37
    @38
    readdcld
    @23
    @40
    @41
    @42
    @45
    simp3d
    @23
    cB
    @5
    cmin
    co
    @15
    cle
    wbr
    cB
    @30
    cle
    wbr
    @23
    cA
    @5
    cB
    @39
    @37
    @47
    @23
    @31
    @32
    @33
    @36
    simp2d
    lesub2dd
    @23
    cB
    @5
    @15
    @47
    @37
    @38
    lesubadd2d
    mpbid
    letrd
    @23
    @4
    @5
    @15
    @46
    @37
    @38
    absdifled
    mpbir2and
    eqbrtrd
    ralrimivva
    @9
    @18
    vr
    @15
    cr
    @7
    @15
    wceq
    @8
    @17
    vx
    vy
    cJ
    cJ
    @7
    @15
    @6
    cle
    breq2
    2ralbidv
    rspcev
    syl2anc
    vr
    vx
    vy
    cM
    cJ
    isbnd3b
    sylanbrc
end
