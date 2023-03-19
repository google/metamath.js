include "cnq.mm"
include "cltq.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cmi.mm"
include "co.mm"
include "clti.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "cnpi.mm"
include "wb.mm"
include "cxp.mm"
include "elpqn.mm"
include "adantr.mm"
include "xp1st.mm"
include "syl.mm"
include "adantl.mm"
include "xp2nd.mm"
include "mulclpi.mm"
include "syl2anc.mm"
include "wor.mm"
include "ltsopi.mm"
include "sotric.mm"
include "mpan.mm"
include "ordpinq.mm"
include "fveq2.mm"
include "eqcomd.mm"
include "oveq12d.mm"
include "ceq.mm"
include "enqbreq2.mm"
include "syl2an.mm"
include "enqeq.mm"
include "3expia.mm"
include "sylbird.mm"
include "impbid2.mm"
include "ancoms.mm"
include "orbi12d.mm"
include "notbid.mm"
include "3bitr4d.mm"
include "w3a.mm"
include "3adant3.mm"
include "3ad2ant3.mm"
include "ltmpi.mm"
include "3syl.mm"
include "bitrd.mm"
include "3adant1.mm"
include "3ad2ant1.mm"
include "anbi12d.mm"
include "fvex.mm"
include "mulcompi.mm"
include "mulasspi.mm"
include "caov13.mm"
include "breq12i.mm"
include "ltrelpi.mm"
include "sotri.mm"
include "syl5eqbrr.mm"
include "sylan2b.mm"
include "syl6bi.mm"
include "3adant2.mm"
include "3ad2ant2.mm"
include "sylibrd.mm"
include "isso2i.mm"

theorem ltsonq
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- <Q Or Q.

  proof
    vx
    vy
    vz
    cnq
    cltq
    vx
    cv
    #
    cnq
    wcel
    #
    vy
    cv
    #
    cnq
    wcel
    #
    wa
    #
    @0
    c1st
    cfv
    #
    @2
    c2nd
    cfv
    #
    cmi
    co
    #
    @2
    c1st
    cfv
    #
    @0
    c2nd
    cfv
    #
    cmi
    co
    #
    clti
    wbr
    #
    @7
    @10
    wceq
    #
    @10
    @7
    clti
    wbr
    #
    wo
    #
    wn
    #
    @0
    @2
    cltq
    wbr
    #
    @0
    @2
    wceq
    #
    @2
    @0
    cltq
    wbr
    #
    wo
    #
    wn
    @4
    @7
    cnpi
    wcel
    #
    @10
    cnpi
    wcel
    #
    @11
    @15
    wb
    #
    @4
    @5
    cnpi
    wcel
    #
    @6
    cnpi
    wcel
    #
    @20
    @4
    @0
    cnpi
    cnpi
    cxp
    #
    wcel
    #
    @23
    @1
    @26
    @3
    @0
    elpqn
    #
    adantr
    #
    @0
    cnpi
    cnpi
    xp1st
    syl
    @4
    @2
    @25
    wcel
    #
    @24
    @3
    @29
    @1
    @2
    elpqn
    #
    adantl
    #
    @2
    cnpi
    cnpi
    xp2nd
    #
    syl
    @5
    @6
    mulclpi
    syl2anc
    @4
    @8
    cnpi
    wcel
    #
    @9
    cnpi
    wcel
    #
    @21
    @4
    @29
    @33
    @31
    @2
    cnpi
    cnpi
    xp1st
    syl
    @4
    @26
    @34
    @28
    @0
    cnpi
    cnpi
    xp2nd
    #
    syl
    @8
    @9
    mulclpi
    syl2anc
    cnpi
    clti
    wor
    @20
    @21
    wa
    @22
    ltsopi
    cnpi
    @7
    @10
    clti
    sotric
    mpan
    syl2anc
    @0
    @2
    ordpinq
    #
    @4
    @19
    @14
    @4
    @17
    @12
    @18
    @13
    @4
    @17
    @12
    @17
    @5
    @8
    @6
    @9
    cmi
    @0
    @2
    c1st
    fveq2
    @17
    @9
    @6
    @0
    @2
    c2nd
    fveq2
    eqcomd
    oveq12d
    @4
    @12
    @0
    @2
    ceq
    wbr
    #
    @17
    @1
    @26
    @29
    @37
    @12
    wb
    @3
    @27
    @30
    @0
    @2
    enqbreq2
    syl2an
    @1
    @3
    @37
    @17
    @0
    @2
    enqeq
    3expia
    sylbird
    impbid2
    @3
    @1
    @18
    @13
    wb
    @2
    @0
    ordpinq
    ancoms
    orbi12d
    notbid
    3bitr4d
    @1
    @3
    vz
    cv
    #
    cnq
    wcel
    #
    w3a
    #
    @16
    @2
    @38
    cltq
    wbr
    #
    wa
    #
    @6
    @5
    @38
    c2nd
    cfv
    #
    cmi
    co
    #
    cmi
    co
    #
    @6
    @38
    c1st
    cfv
    #
    @9
    cmi
    co
    #
    cmi
    co
    #
    clti
    wbr
    #
    @0
    @38
    cltq
    wbr
    #
    @40
    @42
    @43
    @7
    cmi
    co
    #
    @43
    @10
    cmi
    co
    #
    clti
    wbr
    #
    @9
    @8
    @43
    cmi
    co
    #
    cmi
    co
    #
    @9
    @46
    @6
    cmi
    co
    #
    cmi
    co
    #
    clti
    wbr
    #
    wa
    @49
    @40
    @16
    @53
    @41
    @58
    @40
    @16
    @11
    @53
    @1
    @3
    @16
    @11
    wb
    @39
    @36
    3adant3
    @40
    @38
    @25
    wcel
    #
    @43
    cnpi
    wcel
    @11
    @53
    wb
    @39
    @1
    @59
    @3
    @38
    elpqn
    3ad2ant3
    @38
    cnpi
    cnpi
    xp2nd
    @7
    @10
    @43
    ltmpi
    3syl
    bitrd
    @40
    @41
    @54
    @56
    clti
    wbr
    #
    @58
    @3
    @39
    @41
    @60
    wb
    @1
    @2
    @38
    ordpinq
    3adant1
    @40
    @26
    @34
    @60
    @58
    wb
    @1
    @3
    @26
    @39
    @27
    3ad2ant1
    @35
    @54
    @56
    @9
    ltmpi
    3syl
    bitrd
    anbi12d
    @58
    @53
    @52
    @48
    clti
    wbr
    #
    @49
    @55
    @52
    @57
    @48
    clti
    vr
    vs
    vt
    @9
    @8
    @43
    cmi
    @0
    c2nd
    fvex
    #
    @2
    c1st
    fvex
    @38
    c2nd
    fvex
    #
    vr
    cv
    #
    vs
    cv
    #
    mulcompi
    #
    @64
    @65
    vt
    cv
    mulasspi
    #
    caov13
    vr
    vs
    vt
    @9
    @46
    @6
    cmi
    @62
    @38
    c1st
    fvex
    @2
    c2nd
    fvex
    #
    @66
    @67
    caov13
    breq12i
    @53
    @61
    wa
    @45
    @51
    @48
    clti
    vr
    vs
    vt
    @43
    @5
    @6
    cmi
    @63
    @0
    c1st
    fvex
    @68
    @66
    @67
    caov13
    @51
    @52
    @48
    clti
    cnpi
    ltsopi
    ltrelpi
    sotri
    syl5eqbrr
    sylan2b
    syl6bi
    @40
    @50
    @44
    @47
    clti
    wbr
    #
    @49
    @1
    @39
    @50
    @69
    wb
    @3
    @0
    @38
    ordpinq
    3adant2
    @40
    @29
    @24
    @69
    @49
    wb
    @3
    @1
    @29
    @39
    @30
    3ad2ant2
    @32
    @44
    @47
    @6
    ltmpi
    3syl
    bitrd
    sylibrd
    isso2i
end
