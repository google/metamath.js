include "wcel.mm"
include "cvv.mm"
include "cop.mm"
include "crngo.mm"
include "cablo.mm"
include "cxp.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wbr.mm"
include "df-br.mm"
include "relrngo.mm"
include "brrelexi.mm"
include "sylbir.mm"
include "a1i.mm"
include "elex.mm"
include "ad2antrr.mm"
include "wb.mm"
include "crn.mm"
include "copab.mm"
include "df-rngo.mm"
include "eleq2i.mm"
include "simpl.mm"
include "eleq1d.mm"
include "simpr.mm"
include "rneqd.mm"
include "syl6eqr.mm"
include "sqxpeqd.mm"
include "feq123d.mm"
include "anbi12d.mm"
include "oveqd.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "3anbi123d.mm"
include "raleqbidv.mm"
include "eqeq1d.mm"
include "rexeqbidv.mm"
include "opelopabga.mm"
include "syl5bb.mm"
include "expcom.mm"
include "pm5.21ndd.mm"

theorem isrngo
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cG: class G
  let cH: class H
  let cX: class X
  let vg: setvar g
  let vh: setvar h
  assume isring.1: |- X = ran G

  disjoint x y
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint g h
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint G g
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint G h
  disjoint H g
  disjoint H h
  disjoint X g
  disjoint X h
  assert |- ( H e. A -> ( <. G , H >. e. RingOps <-> ( ( G e. AbelOp /\ H : ( X X. X ) --> X ) /\ ( A. x e. X A. y e. X A. z e. X ( ( ( x H y ) H z ) = ( x H ( y H z ) ) /\ ( x H ( y G z ) ) = ( ( x H y ) G ( x H z ) ) /\ ( ( x G y ) H z ) = ( ( x H z ) G ( y H z ) ) ) /\ E. x e. X A. y e. X ( ( x H y ) = y /\ ( y H x ) = y ) ) ) ) )

  proof
    cH
    cA
    wcel
    #
    cG
    cvv
    wcel
    #
    cG
    cH
    cop
    #
    crngo
    wcel
    #
    cG
    cablo
    wcel
    #
    cX
    cX
    cxp
    #
    cX
    cH
    wf
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    vz
    cv
    #
    cH
    co
    #
    @8
    @9
    @11
    cH
    co
    #
    cH
    co
    #
    wceq
    #
    @8
    @9
    @11
    cG
    co
    #
    cH
    co
    #
    @10
    @8
    @11
    cH
    co
    #
    cG
    co
    #
    wceq
    #
    @8
    @9
    cG
    co
    #
    @11
    cH
    co
    #
    @18
    @13
    cG
    co
    #
    wceq
    #
    w3a
    #
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
    @10
    @9
    wceq
    #
    @9
    @8
    cH
    co
    #
    @9
    wceq
    #
    wa
    #
    vy
    cX
    wral
    #
    vx
    cX
    wrex
    #
    wa
    #
    wa
    #
    @3
    @1
    wi
    @0
    @3
    cG
    cH
    crngo
    wbr
    @1
    cG
    cH
    crngo
    df-br
    cG
    cH
    crngo
    relrngo
    brrelexi
    sylbir
    a1i
    @36
    @1
    wi
    @0
    @4
    @1
    @6
    @35
    cG
    cablo
    elex
    ad2antrr
    a1i
    @1
    @0
    @3
    @36
    wb
    @3
    @2
    vg
    cv
    #
    cablo
    wcel
    #
    @37
    crn
    #
    @39
    cxp
    #
    @39
    vh
    cv
    #
    wf
    #
    wa
    #
    @8
    @9
    @41
    co
    #
    @11
    @41
    co
    #
    @8
    @9
    @11
    @41
    co
    #
    @41
    co
    #
    wceq
    #
    @8
    @9
    @11
    @37
    co
    #
    @41
    co
    #
    @44
    @8
    @11
    @41
    co
    #
    @37
    co
    #
    wceq
    #
    @8
    @9
    @37
    co
    #
    @11
    @41
    co
    #
    @51
    @46
    @37
    co
    #
    wceq
    #
    w3a
    #
    vz
    @39
    wral
    #
    vy
    @39
    wral
    #
    vx
    @39
    wral
    #
    @44
    @9
    wceq
    #
    @9
    @8
    @41
    co
    #
    @9
    wceq
    #
    wa
    #
    vy
    @39
    wral
    #
    vx
    @39
    wrex
    #
    wa
    #
    wa
    #
    vg
    vh
    copab
    #
    wcel
    @1
    @0
    wa
    @36
    crngo
    @70
    @2
    vx
    vy
    vz
    vg
    vh
    df-rngo
    eleq2i
    @69
    @36
    vg
    vh
    cG
    cH
    cvv
    cA
    @37
    cG
    wceq
    #
    @41
    cH
    wceq
    #
    wa
    #
    @43
    @7
    @68
    @35
    @73
    @38
    @4
    @42
    @6
    @73
    @37
    cG
    cablo
    @71
    @72
    simpl
    #
    eleq1d
    @73
    @40
    @5
    @39
    cX
    @41
    cH
    @71
    @72
    simpr
    #
    @73
    @39
    cX
    @73
    @39
    cG
    crn
    cX
    @73
    @37
    cG
    @74
    rneqd
    isring.1
    syl6eqr
    #
    sqxpeqd
    @76
    feq123d
    anbi12d
    @73
    @61
    @28
    @67
    @34
    @73
    @60
    @27
    vx
    @39
    cX
    @76
    @73
    @59
    @26
    vy
    @39
    cX
    @76
    @73
    @58
    @25
    vz
    @39
    cX
    @76
    @73
    @48
    @15
    @53
    @20
    @57
    @24
    @73
    @45
    @12
    @47
    @14
    @73
    @44
    @10
    @11
    @11
    @41
    cH
    @75
    @73
    @41
    cH
    @8
    @9
    @75
    oveqd
    #
    @73
    @11
    eqidd
    #
    oveq123d
    @73
    @8
    @8
    @46
    @13
    @41
    cH
    @75
    @73
    @8
    eqidd
    #
    @73
    @41
    cH
    @9
    @11
    @75
    oveqd
    #
    oveq123d
    eqeq12d
    @73
    @50
    @17
    @52
    @19
    @73
    @8
    @8
    @49
    @16
    @41
    cH
    @75
    @79
    @73
    @37
    cG
    @9
    @11
    @74
    oveqd
    oveq123d
    @73
    @44
    @10
    @51
    @18
    @37
    cG
    @74
    @77
    @73
    @41
    cH
    @8
    @11
    @75
    oveqd
    #
    oveq123d
    eqeq12d
    @73
    @55
    @22
    @56
    @23
    @73
    @54
    @21
    @11
    @11
    @41
    cH
    @75
    @73
    @37
    cG
    @8
    @9
    @74
    oveqd
    @78
    oveq123d
    @73
    @51
    @18
    @46
    @13
    @37
    cG
    @74
    @81
    @80
    oveq123d
    eqeq12d
    3anbi123d
    raleqbidv
    raleqbidv
    raleqbidv
    @73
    @66
    @33
    vx
    @39
    cX
    @76
    @73
    @65
    @32
    vy
    @39
    cX
    @76
    @73
    @62
    @29
    @64
    @31
    @73
    @44
    @10
    @9
    @77
    eqeq1d
    @73
    @63
    @30
    @9
    @73
    @41
    cH
    @9
    @8
    @75
    oveqd
    eqeq1d
    anbi12d
    raleqbidv
    rexeqbidv
    anbi12d
    anbi12d
    opelopabga
    syl5bb
    expcom
    pm5.21ndd
end
