include "wcel.mm"
include "cgr.mm"
include "cv.mm"
include "crn.mm"
include "wceq.mm"
include "cxp.mm"
include "wf.mm"
include "co.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "w3a.mm"
include "wex.mm"
include "feq1.mm"
include "oveq.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "2ralbidv.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "anbi12d.mm"
include "rexralbidv.mm"
include "3anbi123d.mm"
include "exbidv.mm"
include "df-grpo.mm"
include "elab2g.mm"
include "wfo.mm"
include "simpl.mm"
include "ralimi.mm"
include "oveq2.mm"
include "id.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "rspcv.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "ex.mm"
include "syld.mm"
include "syl5.mm"
include "reximdv.mm"
include "impcom.mm"
include "ralrimiva.mm"
include "anim2i.mm"
include "foov.mm"
include "sylibr.mm"
include "forn.mm"
include "eqcomd.mm"
include "syl.mm"
include "3adant2.mm"
include "pm4.71ri.mm"
include "exbii.mm"
include "cvv.mm"
include "wb.mm"
include "rnexg.mm"
include "eqeq2i.mm"
include "xpeq1.mm"
include "xpeq2.mm"
include "feq2d.mm"
include "feq3.mm"
include "bitrd.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "rexeq.mm"
include "anbi2d.mm"
include "rexeqbi1dv.mm"
include "sylbir.mm"
include "ceqsexgv.mm"

theorem isgrpo
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let cA: class A
  let cG: class G
  let cX: class X
  let vg: setvar g
  let vt: setvar t
  assume isgrp.1: |- X = ran G

  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint x y
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint g t
  disjoint g u
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint G g
  disjoint t u
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint G t
  disjoint X g
  disjoint X t
  assert |- ( G e. A -> ( G e. GrpOp <-> ( G : ( X X. X ) --> X /\ A. x e. X A. y e. X A. z e. X ( ( x G y ) G z ) = ( x G ( y G z ) ) /\ E. u e. X A. x e. X ( ( u G x ) = x /\ E. y e. X ( y G x ) = u ) ) ) )

  proof
    cG
    cA
    wcel
    #
    cG
    cgr
    wcel
    #
    vt
    cv
    #
    cG
    crn
    #
    wceq
    #
    @2
    @2
    cxp
    #
    @2
    cG
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    #
    vz
    cv
    #
    cG
    co
    #
    @7
    @8
    @10
    cG
    co
    #
    cG
    co
    #
    wceq
    #
    vz
    @2
    wral
    #
    vy
    @2
    wral
    #
    vx
    @2
    wral
    #
    vu
    cv
    #
    @7
    cG
    co
    #
    @7
    wceq
    #
    @8
    @7
    cG
    co
    #
    @18
    wceq
    #
    vy
    @2
    wrex
    #
    wa
    #
    vx
    @2
    wral
    #
    vu
    @2
    wrex
    #
    w3a
    #
    wa
    #
    vt
    wex
    #
    cX
    cX
    cxp
    #
    cX
    cG
    wf
    #
    @14
    vz
    cX
    wral
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    @20
    @22
    vy
    cX
    wrex
    #
    wa
    #
    vx
    cX
    wral
    #
    vu
    cX
    wrex
    #
    w3a
    #
    @0
    @1
    @27
    vt
    wex
    #
    @29
    @5
    @2
    vg
    cv
    #
    wf
    #
    @7
    @8
    @41
    co
    #
    @10
    @41
    co
    #
    @7
    @8
    @10
    @41
    co
    #
    @41
    co
    #
    wceq
    #
    vz
    @2
    wral
    #
    vy
    @2
    wral
    vx
    @2
    wral
    #
    @18
    @7
    @41
    co
    #
    @7
    wceq
    #
    @8
    @7
    @41
    co
    #
    @18
    wceq
    #
    vy
    @2
    wrex
    #
    wa
    #
    vx
    @2
    wral
    vu
    @2
    wrex
    #
    w3a
    #
    vt
    wex
    @40
    vg
    cG
    cgr
    cA
    @41
    cG
    wceq
    #
    @57
    @27
    vt
    @58
    @42
    @6
    @49
    @17
    @56
    @26
    @5
    @2
    @41
    cG
    feq1
    @58
    @48
    @15
    vx
    vy
    @2
    @2
    @58
    @47
    @14
    vz
    @2
    @58
    @44
    @11
    @46
    @13
    @58
    @44
    @43
    @10
    cG
    co
    @11
    @43
    @10
    @41
    cG
    oveq
    @58
    @43
    @9
    @10
    cG
    @7
    @8
    @41
    cG
    oveq
    oveq1d
    eqtrd
    @58
    @46
    @7
    @45
    cG
    co
    @13
    @7
    @45
    @41
    cG
    oveq
    @58
    @45
    @12
    @7
    cG
    @8
    @10
    @41
    cG
    oveq
    oveq2d
    eqtrd
    eqeq12d
    ralbidv
    2ralbidv
    @58
    @55
    @24
    vu
    vx
    @2
    @2
    @58
    @51
    @20
    @54
    @23
    @58
    @50
    @19
    @7
    @18
    @7
    @41
    cG
    oveq
    eqeq1d
    @58
    @53
    @22
    vy
    @2
    @58
    @52
    @21
    @18
    @8
    @7
    @41
    cG
    oveq
    eqeq1d
    rexbidv
    anbi12d
    rexralbidv
    3anbi123d
    exbidv
    vx
    vy
    vz
    vu
    vt
    vg
    df-grpo
    elab2g
    @27
    @28
    vt
    @27
    @4
    @6
    @26
    @4
    @17
    @6
    @26
    wa
    #
    @5
    @2
    cG
    wfo
    #
    @4
    @59
    @6
    @10
    @18
    @8
    cG
    co
    #
    wceq
    #
    vy
    @2
    wrex
    #
    vu
    @2
    wrex
    #
    vz
    @2
    wral
    #
    wa
    @60
    @26
    @65
    @6
    @26
    @64
    vz
    @2
    @10
    @2
    wcel
    #
    @26
    @64
    @66
    @25
    @63
    vu
    @2
    @25
    @20
    vx
    @2
    wral
    #
    @66
    @63
    @24
    @20
    vx
    @2
    @20
    @23
    simpl
    ralimi
    @66
    @67
    @10
    @18
    @10
    cG
    co
    #
    wceq
    #
    @63
    @20
    @69
    vx
    @10
    @2
    @7
    @10
    wceq
    #
    @20
    @68
    @10
    wceq
    @69
    @70
    @19
    @68
    @7
    @10
    @7
    @10
    @18
    cG
    oveq2
    @70
    id
    eqeq12d
    @68
    @10
    eqcom
    syl6bb
    rspcv
    @66
    @69
    @63
    @62
    @69
    vy
    @10
    @2
    @8
    @10
    wceq
    @61
    @68
    @10
    @8
    @10
    @18
    cG
    oveq2
    eqeq2d
    rspcev
    ex
    syld
    syl5
    reximdv
    impcom
    ralrimiva
    anim2i
    vu
    vy
    vz
    @2
    @2
    @2
    cG
    foov
    sylibr
    @60
    @3
    @2
    @5
    @2
    cG
    forn
    eqcomd
    syl
    3adant2
    pm4.71ri
    exbii
    syl6bb
    @0
    @3
    cvv
    wcel
    @29
    @39
    wb
    cG
    cA
    rnexg
    @27
    @39
    vt
    @3
    cvv
    @4
    @2
    cX
    wceq
    #
    @27
    @39
    wb
    cX
    @3
    @2
    isgrp.1
    eqeq2i
    @71
    @6
    @31
    @17
    @34
    @26
    @38
    @71
    @6
    @30
    @2
    cG
    wf
    @31
    @71
    @5
    @30
    @2
    cG
    @71
    @5
    cX
    @2
    cxp
    @30
    @2
    cX
    @2
    xpeq1
    @2
    cX
    cX
    xpeq2
    eqtrd
    feq2d
    @2
    cX
    @30
    cG
    feq3
    bitrd
    @16
    @33
    vx
    @2
    cX
    @15
    @32
    vy
    @2
    cX
    @14
    vz
    @2
    cX
    raleq
    raleqbi1dv
    raleqbi1dv
    @25
    @37
    vu
    @2
    cX
    @24
    @36
    vx
    @2
    cX
    @71
    @23
    @35
    @20
    @22
    vy
    @2
    cX
    rexeq
    anbi2d
    raleqbi1dv
    rexeqbi1dv
    3anbi123d
    sylbir
    ceqsexgv
    syl
    bitrd
end
