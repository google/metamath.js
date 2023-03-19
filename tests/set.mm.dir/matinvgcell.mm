include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "c0g.mm"
include "cfv.mm"
include "csg.mm"
include "co.mm"
include "wceq.mm"
include "cgrp.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "adantl.mm"
include "simpl.mm"
include "matgrp.mm"
include "syl2anc.mm"
include "eqid.mm"
include "grpidcl.mm"
include "syl.mm"
include "simpr.mm"
include "jca.mm"
include "3adant3.mm"
include "matsubgcell.mm"
include "syld3an2.mm"
include "grpinvval2.mm"
include "oveqd.mm"
include "cbs.mm"
include "ringgrp.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "3ad2ant2.mm"
include "df-3an.mm"
include "sylanbrc.mm"
include "matecl.mm"
include "cmpt2.mm"
include "anim1i.mm"
include "ancoms.mm"
include "mat0op.mm"
include "cv.mm"
include "eqidd.mm"
include "simp3r.mm"
include "fvexd.mm"
include "ovmpt2d.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"

theorem matinvgcell
  let cA: class A
  let cB: class B
  let cR: class R
  let cI: class I
  let cJ: class J
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume matplusgcell.a: |- A = ( N Mat R )
  assume matplusgcell.b: |- B = ( Base ` A )
  assume matinvgcell.v: |- V = ( invg ` R )
  assume matinvgcell.w: |- W = ( invg ` A )


  assert |- ( ( R e. Ring /\ X e. B /\ ( I e. N /\ J e. N ) ) -> ( I ( W ` X ) J ) = ( V ` ( I X J ) ) )

  proof
    cR
    crg
    wcel
    #
    cX
    cB
    wcel
    #
    cI
    cN
    wcel
    #
    cJ
    cN
    wcel
    #
    wa
    #
    w3a
    #
    cI
    cJ
    cA
    c0g
    cfv
    #
    cX
    cA
    csg
    cfv
    #
    co
    #
    co
    #
    cI
    cJ
    @6
    co
    #
    cI
    cJ
    cX
    co
    #
    cR
    csg
    cfv
    #
    co
    #
    cI
    cJ
    cX
    cW
    cfv
    #
    co
    @11
    cV
    cfv
    #
    @0
    @6
    cB
    wcel
    #
    @1
    wa
    #
    @1
    @4
    @9
    @13
    wceq
    @0
    @1
    @17
    @4
    @0
    @1
    wa
    #
    @16
    @1
    @18
    cA
    cgrp
    wcel
    #
    @16
    @18
    cN
    cfn
    wcel
    #
    @0
    @19
    @1
    @20
    @0
    @1
    @20
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cX
    matplusgcell.a
    matplusgcell.b
    matrcl
    simpld
    #
    adantl
    @0
    @1
    simpl
    cA
    cR
    cN
    matplusgcell.a
    matgrp
    syl2anc
    #
    cB
    cA
    @6
    matplusgcell.b
    @6
    eqid
    #
    grpidcl
    syl
    @0
    @1
    simpr
    #
    jca
    3adant3
    cA
    cB
    cR
    @7
    cI
    cJ
    @12
    cN
    @6
    cX
    matplusgcell.a
    matplusgcell.b
    @7
    eqid
    #
    @12
    eqid
    #
    matsubgcell
    syld3an2
    @5
    @14
    @8
    cI
    cJ
    @0
    @1
    @14
    @8
    wceq
    #
    @4
    @18
    @19
    @1
    @27
    @22
    @24
    cB
    cA
    @7
    cW
    cX
    @6
    matplusgcell.b
    @25
    matinvgcell.w
    @23
    grpinvval2
    syl2anc
    3adant3
    oveqd
    @5
    @15
    cR
    c0g
    cfv
    #
    @11
    @12
    co
    #
    @13
    @5
    cR
    cgrp
    wcel
    #
    @11
    cR
    cbs
    cfv
    #
    wcel
    #
    @15
    @29
    wceq
    @0
    @1
    @30
    @4
    cR
    ringgrp
    3ad2ant1
    @5
    @2
    @3
    cX
    cA
    cbs
    cfv
    #
    wcel
    #
    w3a
    #
    @32
    @5
    @4
    @34
    @35
    @0
    @1
    @4
    simp3
    #
    @1
    @0
    @34
    @4
    @1
    @34
    cB
    @33
    cX
    matplusgcell.b
    eleq2i
    biimpi
    3ad2ant2
    @2
    @3
    @34
    df-3an
    sylanbrc
    cA
    cR
    cI
    cJ
    @31
    cX
    cN
    matplusgcell.a
    @31
    eqid
    #
    matecl
    syl
    @31
    cR
    @12
    cV
    @11
    @28
    @37
    @26
    matinvgcell.v
    @28
    eqid
    #
    grpinvval2
    syl2anc
    @5
    @28
    @10
    @11
    @12
    @5
    @10
    @28
    @5
    vx
    vy
    cI
    cJ
    cN
    cN
    @28
    @28
    @6
    cvv
    @0
    @1
    @6
    vx
    vy
    cN
    cN
    @28
    cmpt2
    wceq
    #
    @4
    @18
    @20
    @0
    wa
    #
    @39
    @1
    @0
    @40
    @1
    @20
    @0
    @21
    anim1i
    ancoms
    cA
    cR
    vx
    vy
    cN
    @28
    matplusgcell.a
    @38
    mat0op
    syl
    3adant3
    @5
    vx
    cv
    cI
    wceq
    vy
    cv
    cJ
    wceq
    wa
    wa
    @28
    eqidd
    @5
    @2
    @3
    @36
    simpld
    @0
    @1
    @2
    @3
    simp3r
    @5
    cR
    c0g
    fvexd
    ovmpt2d
    eqcomd
    oveq1d
    eqtrd
    3eqtr4d
end
