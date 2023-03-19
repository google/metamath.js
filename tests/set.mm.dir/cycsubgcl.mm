include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "csubg.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "cminusg.mm"
include "cz.mm"
include "wf.mm"
include "mulgcl.mm"
include "3expa.mm"
include "an32s.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"
include "c1.mm"
include "wceq.mm"
include "1z.mm"
include "oveq1.mm"
include "ovex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "mulg1.mm"
include "adantl.mm"
include "syl5eq.mm"
include "wfn.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "sylancl.mm"
include "eqeltrrd.mm"
include "ne0i.mm"
include "caddc.mm"
include "w3a.mm"
include "df-3an.mm"
include "eqid.mm"
include "mulgdir.mm"
include "sylan2br.mm"
include "anass1rs.mm"
include "zaddcl.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "syl2an.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "wb.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "ralrn.mm"
include "adantr.mm"
include "mpbird.mm"
include "cneg.mm"
include "mulgneg.mm"
include "znegcl.mm"
include "fveq2d.mm"
include "jca.mm"
include "ralbidv.mm"
include "fveq2.mm"
include "anbi12d.mm"
include "issubg2.mm"
include "mpbir3and.mm"

theorem cycsubgcl
  let vx: setvar x
  let cA: class A
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let cS: class S
  assume cycsubg.x: |- X = ( Base ` G )
  assume cycsubg.t: |- .x. = ( .g ` G )
  assume cycsubg.f: |- F = ( x e. ZZ |-> ( x .x. A ) )

  disjoint A x
  disjoint G x
  disjoint .x. x
  disjoint X x
  disjoint m n
  disjoint m s
  disjoint m x
  disjoint A m
  disjoint n s
  disjoint n x
  disjoint A n
  disjoint s x
  disjoint A s
  disjoint m u
  disjoint m v
  disjoint G m
  disjoint n u
  disjoint n v
  disjoint G n
  disjoint s u
  disjoint s v
  disjoint G s
  disjoint u v
  disjoint u x
  disjoint G u
  disjoint v x
  disjoint G v
  disjoint S x
  disjoint X m
  disjoint X n
  disjoint F m
  disjoint F n
  disjoint F s
  disjoint F u
  disjoint F v
  assert |- ( ( G e. Grp /\ A e. X ) -> ( ran F e. ( SubGrp ` G ) /\ A e. ran F ) )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cF
    crn
    #
    cG
    csubg
    cfv
    wcel
    #
    cA
    @3
    wcel
    #
    @2
    @4
    @3
    cX
    wss
    #
    @3
    c0
    wne
    #
    vu
    cv
    #
    vv
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @3
    wcel
    #
    vv
    @3
    wral
    #
    @8
    cG
    cminusg
    cfv
    #
    cfv
    #
    @3
    wcel
    #
    wa
    #
    vu
    @3
    wral
    #
    @2
    cz
    cX
    cF
    wf
    #
    @6
    @2
    vx
    cz
    vx
    cv
    #
    cA
    c.x
    co
    #
    cX
    cF
    @0
    @20
    cz
    wcel
    #
    @1
    @21
    cX
    wcel
    #
    @0
    @22
    @1
    @23
    cX
    c.x
    cG
    @20
    cA
    cycsubg.x
    cycsubg.t
    mulgcl
    3expa
    an32s
    cycsubg.f
    fmptd
    #
    cz
    cX
    cF
    frn
    syl
    @2
    @5
    @7
    @2
    c1
    cF
    cfv
    #
    cA
    @3
    @2
    @25
    c1
    cA
    c.x
    co
    #
    cA
    c1
    cz
    wcel
    #
    @25
    @26
    wceq
    1z
    vx
    c1
    @21
    @26
    cz
    cF
    @20
    c1
    cA
    c.x
    oveq1
    cycsubg.f
    c1
    cA
    c.x
    ovex
    fvmpt
    ax-mp
    @1
    @26
    cA
    wceq
    @0
    cX
    c.x
    cG
    cA
    cycsubg.x
    cycsubg.t
    mulg1
    adantl
    syl5eq
    @2
    cF
    cz
    wfn
    #
    @27
    @25
    @3
    wcel
    @2
    @19
    @28
    @24
    cz
    cX
    cF
    ffn
    syl
    #
    1z
    cz
    c1
    cF
    fnfvelrn
    sylancl
    eqeltrrd
    #
    @3
    cA
    ne0i
    syl
    @2
    @18
    vm
    cv
    #
    cF
    cfv
    #
    @9
    @10
    co
    #
    @3
    wcel
    #
    vv
    @3
    wral
    #
    @32
    @14
    cfv
    #
    @3
    wcel
    #
    wa
    #
    vm
    cz
    wral
    #
    @2
    @38
    vm
    cz
    @2
    @31
    cz
    wcel
    #
    wa
    #
    @35
    @37
    @41
    @35
    @32
    vn
    cv
    #
    cF
    cfv
    #
    @10
    co
    #
    @3
    wcel
    #
    vn
    cz
    wral
    #
    @41
    @45
    vn
    cz
    @2
    @40
    @42
    cz
    wcel
    #
    @45
    @2
    @40
    @47
    wa
    #
    wa
    #
    @31
    @42
    caddc
    co
    #
    cF
    cfv
    #
    @44
    @3
    @49
    @50
    cA
    c.x
    co
    #
    @31
    cA
    c.x
    co
    #
    @42
    cA
    c.x
    co
    #
    @10
    co
    #
    @51
    @44
    @0
    @48
    @1
    @52
    @55
    wceq
    #
    @48
    @1
    wa
    @0
    @40
    @47
    @1
    w3a
    @56
    @40
    @47
    @1
    df-3an
    cX
    @10
    c.x
    cG
    @31
    @42
    cA
    cycsubg.x
    cycsubg.t
    @10
    eqid
    #
    mulgdir
    sylan2br
    anass1rs
    @49
    @50
    cz
    wcel
    #
    @51
    @52
    wceq
    @48
    @58
    @2
    @31
    @42
    zaddcl
    #
    adantl
    vx
    @50
    @21
    @52
    cz
    cF
    @20
    @50
    cA
    c.x
    oveq1
    cycsubg.f
    @50
    cA
    c.x
    ovex
    fvmpt
    syl
    @49
    @32
    @53
    @43
    @54
    @10
    @40
    @32
    @53
    wceq
    #
    @2
    @47
    vx
    @31
    @21
    @53
    cz
    cF
    @20
    @31
    cA
    c.x
    oveq1
    cycsubg.f
    @31
    cA
    c.x
    ovex
    fvmpt
    #
    ad2antrl
    @47
    @43
    @54
    wceq
    @2
    @40
    vx
    @42
    @21
    @54
    cz
    cF
    @20
    @42
    cA
    c.x
    oveq1
    cycsubg.f
    @42
    cA
    c.x
    ovex
    fvmpt
    ad2antll
    oveq12d
    3eqtr4d
    @2
    @28
    @58
    @51
    @3
    wcel
    @48
    @29
    @59
    cz
    @50
    cF
    fnfvelrn
    syl2an
    eqeltrrd
    anassrs
    ralrimiva
    @2
    @35
    @46
    wb
    #
    @40
    @2
    @28
    @62
    @29
    @34
    @45
    vv
    vn
    cz
    cF
    @9
    @43
    wceq
    @33
    @44
    @3
    @9
    @43
    @32
    @10
    oveq2
    eleq1d
    ralrn
    syl
    adantr
    mpbird
    @41
    @31
    cneg
    #
    cF
    cfv
    #
    @36
    @3
    @41
    @63
    cA
    c.x
    co
    #
    @53
    @14
    cfv
    #
    @64
    @36
    @0
    @40
    @1
    @65
    @66
    wceq
    #
    @0
    @40
    @1
    @67
    cX
    c.x
    cG
    @14
    @31
    cA
    cycsubg.x
    cycsubg.t
    @14
    eqid
    #
    mulgneg
    3expa
    an32s
    @41
    @63
    cz
    wcel
    #
    @64
    @65
    wceq
    @40
    @69
    @2
    @31
    znegcl
    #
    adantl
    vx
    @63
    @21
    @65
    cz
    cF
    @20
    @63
    cA
    c.x
    oveq1
    cycsubg.f
    @63
    cA
    c.x
    ovex
    fvmpt
    syl
    @41
    @32
    @53
    @14
    @40
    @60
    @2
    @61
    adantl
    fveq2d
    3eqtr4d
    @2
    @28
    @69
    @64
    @3
    wcel
    @40
    @29
    @70
    cz
    @63
    cF
    fnfvelrn
    syl2an
    eqeltrrd
    jca
    ralrimiva
    @2
    @28
    @18
    @39
    wb
    @29
    @17
    @38
    vu
    vm
    cz
    cF
    @8
    @32
    wceq
    #
    @13
    @35
    @16
    @37
    @71
    @12
    @34
    vv
    @3
    @71
    @11
    @33
    @3
    @8
    @32
    @9
    @10
    oveq1
    eleq1d
    ralbidv
    @71
    @15
    @36
    @3
    @8
    @32
    @14
    fveq2
    eleq1d
    anbi12d
    ralrn
    syl
    mpbird
    @0
    @4
    @6
    @7
    @18
    w3a
    wb
    @1
    vu
    vv
    cX
    @10
    @3
    cG
    @14
    cycsubg.x
    @57
    @68
    issubg2
    adantr
    mpbir3and
    @30
    jca
end
