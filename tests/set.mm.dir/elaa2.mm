include "caa.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cc.mm"
include "cv.mm"
include "ccoe.mm"
include "cfv.mm"
include "wne.mm"
include "wceq.mm"
include "wa.mm"
include "cz.mm"
include "cply.mm"
include "wrex.mm"
include "aasscn.mm"
include "eldifi.mm"
include "sseldi.mm"
include "c0p.mm"
include "elaa.mm"
include "sylib.mm"
include "simprd.mm"
include "w3a.mm"
include "cdgr.mm"
include "cn0.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "caddc.mm"
include "cmpt.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "3ad2ant1.mm"
include "eldifsni.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "cbvrabv.mm"
include "infeq1i.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "eqid.mm"
include "elaa2lem.mm"
include "rexlimdv3a.mm"
include "mpd.mm"
include "jca.mm"
include "simpl.mm"
include "cxp.mm"
include "coe0.mm"
include "syl6eq.mm"
include "fveq1d.mm"
include "0nn0.mm"
include "fvconst2g.mm"
include "mp2an.mm"
include "adantl.mm"
include "wn.mm"
include "neneq.mm"
include "ad2antlr.mm"
include "pm2.65da.mm"
include "velsn.mm"
include "sylnibr.mm"
include "eldifd.mm"
include "adantrr.mm"
include "simprr.mm"
include "reximi2.mm"
include "anim2i.mm"
include "sylibr.mm"
include "simpr.mm"
include "nfv.mm"
include "nfre1.mm"
include "nfan.mm"
include "wi.mm"
include "simpl3r.mm"
include "coefv0.mm"
include "sylan9eqr.mm"
include "adantlr.mm"
include "simplr.mm"
include "eqnetrd.mm"
include "neneqd.mm"
include "adantlrr.mm"
include "3adantl1.mm"
include "elsng.mm"
include "biimpa.mm"
include "3ad2antl1.mm"
include "mtand.mm"
include "3exp.mm"
include "adantr.mm"
include "rexlimd.mm"
include "impbii.mm"

theorem elaa2
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vz: setvar z
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x

  disjoint A f
  disjoint A g
  disjoint A k
  disjoint A z
  disjoint f g
  disjoint f k
  disjoint f z
  disjoint g k
  disjoint g z
  disjoint k z
  disjoint f j
  disjoint f m
  disjoint g j
  disjoint g m
  disjoint j k
  disjoint j m
  disjoint j z
  disjoint k m
  disjoint m z
  disjoint g n
  disjoint m n
  disjoint k x
  assert |- ( A e. ( AA \ { 0 } ) <-> ( A e. CC /\ E. f e. ( Poly ` ZZ ) ( ( ( coeff ` f ) ` 0 ) =/= 0 /\ ( f ` A ) = 0 ) ) )

  proof
    cA
    caa
    cc0
    csn
    #
    cdif
    wcel
    #
    cA
    cc
    wcel
    #
    cc0
    vf
    cv
    #
    ccoe
    cfv
    #
    cfv
    #
    cc0
    wne
    #
    cA
    @3
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vf
    cz
    cply
    cfv
    #
    wrex
    #
    wa
    #
    @1
    @2
    @11
    @1
    caa
    cc
    cA
    aasscn
    cA
    caa
    @0
    eldifi
    #
    sseldi
    @1
    cA
    vg
    cv
    #
    cfv
    cc0
    wceq
    #
    vg
    @10
    c0p
    csn
    #
    cdif
    #
    wrex
    #
    @11
    @1
    @2
    @18
    @1
    cA
    caa
    wcel
    #
    @2
    @18
    wa
    @13
    cA
    vg
    elaa
    sylib
    simprd
    @1
    @15
    @11
    vg
    @17
    @1
    @14
    @17
    wcel
    #
    @15
    w3a
    vz
    cA
    vf
    vk
    vn
    vz
    cc
    cc0
    @14
    cdgr
    cfv
    vm
    cv
    #
    @14
    ccoe
    cfv
    #
    cfv
    #
    cc0
    wne
    #
    vm
    cn0
    crab
    #
    cr
    clt
    cinf
    #
    cmin
    co
    cfz
    co
    vk
    cv
    #
    vj
    cn0
    vj
    cv
    #
    @26
    caddc
    co
    #
    @22
    cfv
    #
    cmpt
    #
    cfv
    vz
    cv
    @27
    cexp
    co
    cmul
    co
    vk
    csu
    cmpt
    #
    @14
    @31
    @26
    @1
    @20
    @19
    @15
    @13
    3ad2ant1
    @1
    @20
    cA
    cc0
    wne
    @15
    cA
    caa
    cc0
    eldifsni
    3ad2ant1
    @20
    @1
    @14
    @10
    wcel
    @15
    @14
    @10
    @16
    eldifi
    3ad2ant2
    @20
    @1
    @14
    c0p
    wne
    @15
    @14
    @10
    c0p
    eldifsni
    3ad2ant2
    @1
    @20
    @15
    simp3
    cr
    @25
    vn
    cv
    #
    @22
    cfv
    #
    cc0
    wne
    #
    vn
    cn0
    crab
    clt
    @24
    @35
    vm
    vn
    cn0
    @21
    @33
    wceq
    @23
    @34
    cc0
    @21
    @33
    @22
    fveq2
    neeq1d
    cbvrabv
    infeq1i
    vj
    vk
    cn0
    @30
    @27
    @26
    caddc
    co
    #
    @22
    cfv
    @28
    @27
    wceq
    @29
    @36
    @22
    @28
    @27
    @26
    caddc
    oveq1
    fveq2d
    cbvmptv
    @32
    eqid
    elaa2lem
    rexlimdv3a
    mpd
    jca
    @12
    cA
    caa
    @0
    @12
    @2
    @8
    vf
    @17
    wrex
    #
    wa
    @19
    @11
    @37
    @2
    @9
    @8
    vf
    @10
    @17
    @3
    @10
    wcel
    #
    @9
    wa
    @3
    @17
    wcel
    #
    @8
    @38
    @6
    @39
    @8
    @38
    @6
    wa
    #
    @3
    @10
    @16
    @38
    @6
    simpl
    @40
    @3
    c0p
    wceq
    #
    @3
    @16
    wcel
    @40
    @41
    @5
    cc0
    wceq
    #
    @41
    @42
    @40
    @41
    @5
    cc0
    cn0
    @0
    cxp
    #
    cfv
    #
    cc0
    @41
    cc0
    @4
    @43
    @41
    @4
    c0p
    ccoe
    cfv
    @43
    @3
    c0p
    ccoe
    fveq2
    coe0
    syl6eq
    fveq1d
    cc0
    cn0
    wcel
    #
    @45
    @44
    cc0
    wceq
    0nn0
    0nn0
    cn0
    cc0
    cc0
    cn0
    fvconst2g
    mp2an
    syl6eq
    adantl
    @6
    @42
    wn
    @38
    @41
    @5
    cc0
    neneq
    ad2antlr
    pm2.65da
    vf
    c0p
    velsn
    sylnibr
    eldifd
    adantrr
    @38
    @6
    @8
    simprr
    jca
    reximi2
    anim2i
    cA
    vf
    elaa
    sylibr
    @12
    @11
    cA
    @0
    wcel
    #
    wn
    #
    @2
    @11
    simpr
    @12
    @9
    @47
    vf
    @10
    @2
    @11
    vf
    @2
    vf
    nfv
    @9
    vf
    @10
    nfre1
    nfan
    @47
    vf
    nfv
    @2
    @38
    @9
    @47
    wi
    wi
    @11
    @2
    @38
    @9
    @47
    @2
    @38
    @9
    w3a
    #
    @46
    cA
    cc0
    wceq
    #
    @48
    @49
    @8
    @6
    @8
    @2
    @38
    @49
    simpl3r
    @38
    @9
    @49
    @8
    wn
    #
    @2
    @38
    @6
    @49
    @50
    @8
    @40
    @49
    wa
    #
    @7
    cc0
    @51
    @7
    @5
    cc0
    @38
    @49
    @7
    @5
    wceq
    @6
    @49
    @38
    @7
    cc0
    @3
    cfv
    @5
    cA
    cc0
    @3
    fveq2
    @4
    cz
    @3
    @4
    eqid
    coefv0
    sylan9eqr
    adantlr
    @38
    @6
    @49
    simplr
    eqnetrd
    neneqd
    adantlrr
    3adantl1
    pm2.65da
    @2
    @38
    @46
    @49
    @9
    @2
    @46
    @49
    cA
    cc0
    cc
    elsng
    biimpa
    3ad2antl1
    mtand
    3exp
    adantr
    rexlimd
    mpd
    eldifd
    impbii
end
