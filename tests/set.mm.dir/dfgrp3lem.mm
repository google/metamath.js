include "csgrp.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "w3a.mm"
include "wex.mm"
include "simp2.mm"
include "n0.mm"
include "sylib.mm"
include "wi.mm"
include "weq.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "oveq1.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "rspcv.mm"
include "eqeq2.mm"
include "rspcva.mm"
include "cbvrexv.mm"
include "biimpi.mm"
include "adantr.mm"
include "syl.mm"
include "ex.mm"
include "syldc.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "rspc2va.mm"
include "simprd.mm"
include "expcom.mm"
include "impl.mm"
include "ad2ant2r.mm"
include "simpll1.mm"
include "simplr.mm"
include "simpllr.mm"
include "simprr.mm"
include "sgrpass.mm"
include "syl13anc.mm"
include "simprl.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "anassrs.mm"
include "id.mm"
include "eqeq12d.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "adantrl.mm"
include "mpd.mm"
include "simpld.mm"
include "ancoms.mm"
include "com12.mm"
include "adantllr.mm"
include "adantrr.mm"
include "jca.mm"
include "expr.mm"
include "ralrimdva.mm"
include "reximdva.mm"
include "exlimddv.mm"

theorem dfgrp3lem
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cB: class B
  let c.pl: class .+
  let vi: setvar i
  let cG: class G
  let vr: setvar r
  let va: setvar a
  let vl: setvar l
  let vw: setvar w
  let vz: setvar z
  assume dfgrp3.b: |- B = ( Base ` G )
  assume dfgrp3.p: |- .+ = ( +g ` G )

  disjoint B a
  disjoint B i
  disjoint B l
  disjoint B r
  disjoint B u
  disjoint B x
  disjoint B y
  disjoint a i
  disjoint a l
  disjoint a r
  disjoint a u
  disjoint a x
  disjoint a y
  disjoint i l
  disjoint i r
  disjoint i u
  disjoint i x
  disjoint i y
  disjoint l r
  disjoint l u
  disjoint l x
  disjoint l y
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint u x
  disjoint u y
  disjoint x y
  disjoint G a
  disjoint G i
  disjoint G l
  disjoint G r
  disjoint G u
  disjoint G x
  disjoint G y
  disjoint .+ a
  disjoint .+ i
  disjoint .+ l
  disjoint .+ r
  disjoint .+ u
  disjoint .+ x
  disjoint .+ y
  disjoint B w
  disjoint B z
  disjoint a w
  disjoint a z
  disjoint i w
  disjoint i z
  disjoint l w
  disjoint l z
  disjoint r w
  disjoint r z
  disjoint u w
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint G w
  disjoint G z
  disjoint .+ w
  disjoint .+ z
  assert |- ( ( G e. SGrp /\ B =/= (/) /\ A. x e. B A. y e. B ( E. l e. B ( l .+ x ) = y /\ E. r e. B ( x .+ r ) = y ) ) -> E. u e. B A. a e. B ( ( u .+ a ) = a /\ E. i e. B ( i .+ a ) = u ) )

  proof
    cG
    csgrp
    wcel
    #
    cB
    c0
    wne
    #
    vl
    cv
    #
    vx
    cv
    #
    c.pl
    co
    #
    vy
    cv
    #
    wceq
    #
    vl
    cB
    wrex
    #
    @3
    vr
    cv
    #
    c.pl
    co
    #
    @5
    wceq
    #
    vr
    cB
    wrex
    #
    wa
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    w3a
    #
    vw
    cv
    #
    cB
    wcel
    #
    vu
    cv
    #
    va
    cv
    #
    c.pl
    co
    #
    @19
    wceq
    #
    vi
    cv
    #
    @19
    c.pl
    co
    #
    @18
    wceq
    #
    vi
    cB
    wrex
    #
    wa
    #
    va
    cB
    wral
    #
    vu
    cB
    wrex
    #
    vw
    @15
    @1
    @17
    vw
    wex
    @0
    @1
    @14
    simp2
    vw
    cB
    n0
    sylib
    @15
    @17
    wa
    #
    @18
    @16
    c.pl
    co
    #
    @16
    wceq
    #
    vu
    cB
    wrex
    #
    @28
    @15
    @17
    @32
    @14
    @0
    @17
    @32
    wi
    @1
    @17
    @14
    @2
    @16
    c.pl
    co
    #
    @5
    wceq
    #
    vl
    cB
    wrex
    #
    @16
    @8
    c.pl
    co
    #
    @5
    wceq
    #
    vr
    cB
    wrex
    #
    wa
    #
    vy
    cB
    wral
    #
    @32
    @13
    @40
    vx
    @16
    cB
    vx
    vw
    weq
    #
    @12
    @39
    vy
    cB
    @41
    @7
    @35
    @11
    @38
    @41
    @6
    @34
    vl
    cB
    @41
    @4
    @33
    @5
    @3
    @16
    @2
    c.pl
    oveq2
    eqeq1d
    rexbidv
    @41
    @10
    @37
    vr
    cB
    @41
    @9
    @36
    @5
    @3
    @16
    @8
    c.pl
    oveq1
    eqeq1d
    rexbidv
    anbi12d
    #
    ralbidv
    rspcv
    @17
    @40
    @32
    @17
    @40
    wa
    @33
    @16
    wceq
    #
    vl
    cB
    wrex
    #
    @36
    @16
    wceq
    #
    vr
    cB
    wrex
    #
    wa
    #
    @32
    @39
    @47
    vy
    @16
    cB
    vy
    vw
    weq
    #
    @35
    @44
    @38
    @46
    @48
    @34
    @43
    vl
    cB
    @5
    @16
    @33
    eqeq2
    rexbidv
    @48
    @37
    @45
    vr
    cB
    @5
    @16
    @36
    eqeq2
    rexbidv
    anbi12d
    rspcva
    @44
    @32
    @46
    @44
    @32
    @43
    @31
    vl
    vu
    cB
    vl
    vu
    weq
    @33
    @30
    @16
    @2
    @18
    @16
    c.pl
    oveq1
    eqeq1d
    cbvrexv
    biimpi
    adantr
    syl
    ex
    syldc
    3ad2ant3
    imp
    @29
    @31
    @27
    vu
    cB
    @29
    @18
    cB
    wcel
    #
    wa
    #
    @31
    @26
    va
    cB
    @50
    @19
    cB
    wcel
    #
    @31
    @26
    @50
    @51
    @31
    wa
    wa
    #
    @21
    @25
    @52
    @36
    @19
    wceq
    #
    vr
    cB
    wrex
    #
    @21
    @29
    @51
    @54
    @49
    @31
    @15
    @17
    @51
    @54
    @14
    @0
    @17
    @51
    wa
    #
    @54
    wi
    @1
    @55
    @14
    @54
    @55
    @14
    wa
    @33
    @19
    wceq
    #
    vl
    cB
    wrex
    #
    @54
    @12
    @57
    @54
    wa
    @39
    vx
    vy
    @16
    @19
    cB
    cB
    @42
    vy
    va
    weq
    #
    @35
    @57
    @38
    @54
    @58
    @34
    @56
    vl
    cB
    @5
    @19
    @33
    eqeq2
    rexbidv
    @58
    @37
    @53
    vr
    cB
    @5
    @19
    @36
    eqeq2
    rexbidv
    anbi12d
    rspc2va
    simprd
    expcom
    3ad2ant3
    impl
    ad2ant2r
    @50
    @31
    @54
    @21
    wi
    @51
    @54
    @16
    vz
    cv
    #
    c.pl
    co
    #
    @19
    wceq
    #
    vz
    cB
    wrex
    @50
    @31
    wa
    #
    @21
    @53
    @61
    vr
    vz
    cB
    vr
    vz
    weq
    @36
    @60
    @19
    @8
    @59
    @16
    c.pl
    oveq2
    eqeq1d
    cbvrexv
    @62
    @61
    @21
    vz
    cB
    @62
    @59
    cB
    wcel
    #
    wa
    @18
    @60
    c.pl
    co
    #
    @60
    wceq
    #
    @61
    @21
    @50
    @31
    @63
    @65
    @50
    @31
    @63
    wa
    #
    wa
    #
    @30
    @59
    c.pl
    co
    #
    @64
    @60
    @67
    @0
    @49
    @17
    @63
    @68
    @64
    wceq
    @50
    @0
    @66
    @0
    @1
    @14
    @17
    @49
    simpll1
    adantr
    @29
    @49
    @66
    simplr
    @15
    @17
    @49
    @66
    simpllr
    @50
    @31
    @63
    simprr
    cB
    cG
    @18
    @16
    c.pl
    @59
    dfgrp3.b
    dfgrp3.p
    sgrpass
    syl13anc
    @67
    @30
    @16
    @59
    c.pl
    @50
    @31
    @63
    simprl
    oveq1d
    eqtr3d
    anassrs
    @61
    @64
    @20
    @60
    @19
    @60
    @19
    @18
    c.pl
    oveq2
    @61
    id
    eqeq12d
    syl5ibcom
    rexlimdva
    syl5bi
    adantrl
    mpd
    @50
    @51
    @25
    @31
    @15
    @49
    @51
    @25
    @17
    @15
    @49
    wa
    @51
    wa
    @2
    @19
    c.pl
    co
    #
    @18
    wceq
    #
    vl
    cB
    wrex
    #
    @25
    @15
    @49
    @51
    @71
    @14
    @0
    @49
    @51
    wa
    #
    @71
    wi
    @1
    @72
    @14
    @71
    @51
    @49
    @14
    @71
    wi
    @51
    @49
    wa
    #
    @14
    @71
    @73
    @14
    wa
    @71
    @19
    @8
    c.pl
    co
    #
    @18
    wceq
    #
    vr
    cB
    wrex
    #
    @12
    @71
    @76
    wa
    @69
    @5
    wceq
    #
    vl
    cB
    wrex
    #
    @74
    @5
    wceq
    #
    vr
    cB
    wrex
    #
    wa
    vx
    vy
    @19
    @18
    cB
    cB
    vx
    va
    weq
    #
    @7
    @78
    @11
    @80
    @81
    @6
    @77
    vl
    cB
    @81
    @4
    @69
    @5
    @3
    @19
    @2
    c.pl
    oveq2
    eqeq1d
    rexbidv
    @81
    @10
    @79
    vr
    cB
    @81
    @9
    @74
    @5
    @3
    @19
    @8
    c.pl
    oveq1
    eqeq1d
    rexbidv
    anbi12d
    vy
    vu
    weq
    #
    @78
    @71
    @80
    @76
    @82
    @77
    @70
    vl
    cB
    @5
    @18
    @69
    eqeq2
    rexbidv
    @82
    @79
    @75
    vr
    cB
    @5
    @18
    @74
    eqeq2
    rexbidv
    anbi12d
    rspc2va
    simpld
    ex
    ancoms
    com12
    3ad2ant3
    impl
    @70
    @24
    vl
    vi
    cB
    vl
    vi
    weq
    @69
    @23
    @18
    @2
    @22
    @19
    c.pl
    oveq1
    eqeq1d
    cbvrexv
    sylib
    adantllr
    adantrr
    jca
    expr
    ralrimdva
    reximdva
    mpd
    exlimddv
end
