include "clmod.mm"
include "wcel.mm"
include "c1.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "chash.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cpw.mm"
include "c0g.mm"
include "w3a.mm"
include "clindeps.mm"
include "cv.mm"
include "cfsupp.mm"
include "clinc.mm"
include "co.mm"
include "wceq.mm"
include "wne.mm"
include "wrex.mm"
include "cmap.mm"
include "cur.mm"
include "cif.mm"
include "cmpt.mm"
include "eqid.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "cbvmptv.mm"
include "mptcfsupp.mm"
include "3adant1r.mm"
include "simp1l.mm"
include "simp2.mm"
include "linc0scn0.mm"
include "syl2anc.mm"
include "simp3.mm"
include "wb.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "adantl.mm"
include "cvv.mm"
include "fvexd.mm"
include "iftrue.mm"
include "fvmptg.mm"
include "crg.mm"
include "lmodring.mm"
include "anim1i.mm"
include "3ad2ant1.mm"
include "ring1ne0.mm"
include "syl.mm"
include "eqnetrd.mm"
include "rspcedvd.mm"
include "wf.mm"
include "lmod1cl.mm"
include "lmod0cl.mm"
include "ifcld.mm"
include "adantr.mm"
include "fmptd.mm"
include "elmapd.mm"
include "mpbird.mm"
include "breq1.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "fveq1.mm"
include "rexbidv.mm"
include "3anbi123d.mm"
include "rspcedv.mm"
include "mp3and.mm"
include "islindeps.mm"

theorem el0ldep
  let cS: class S
  let cM: class M
  let vf: setvar f
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k


  assert |- ( ( ( M e. LMod /\ 1 < ( # ` ( Base ` ( Scalar ` M ) ) ) ) /\ S e. ~P ( Base ` M ) /\ ( 0g ` M ) e. S ) -> S linDepS M )

  proof
    cM
    clmod
    wcel
    #
    c1
    cM
    csca
    cfv
    #
    cbs
    cfv
    #
    chash
    cfv
    clt
    wbr
    #
    wa
    #
    cS
    cM
    cbs
    cfv
    #
    cpw
    #
    wcel
    #
    cM
    c0g
    cfv
    #
    cS
    wcel
    #
    w3a
    #
    cS
    cM
    clindeps
    wbr
    #
    vf
    cv
    #
    @1
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    @12
    cS
    cM
    clinc
    cfv
    #
    co
    #
    @8
    wceq
    #
    vx
    cv
    #
    @12
    cfv
    #
    @13
    wne
    #
    vx
    cS
    wrex
    #
    w3a
    #
    vf
    @2
    cS
    cmap
    co
    #
    wrex
    #
    @10
    vs
    cS
    vs
    cv
    #
    @8
    wceq
    #
    @1
    cur
    cfv
    #
    @13
    cif
    #
    cmpt
    #
    @13
    cfsupp
    wbr
    #
    @29
    cS
    @15
    co
    #
    @8
    wceq
    #
    @18
    @29
    cfv
    #
    @13
    wne
    #
    vx
    cS
    wrex
    #
    @24
    @0
    @7
    @9
    @30
    @3
    vy
    @5
    @1
    @27
    @29
    cM
    cS
    @8
    @13
    @5
    eqid
    #
    @1
    eqid
    #
    @13
    eqid
    #
    @27
    eqid
    #
    vs
    vy
    cS
    @28
    vy
    cv
    #
    @8
    wceq
    #
    @27
    @13
    cif
    @25
    @40
    wceq
    @26
    @41
    @27
    @13
    @25
    @40
    @8
    eqeq1
    ifbid
    cbvmptv
    mptcfsupp
    3adant1r
    @10
    @0
    @7
    @32
    @0
    @3
    @7
    @9
    simp1l
    #
    @4
    @7
    @9
    simp2
    #
    vs
    @5
    @1
    @27
    @29
    cM
    cS
    @13
    @8
    @36
    @37
    @38
    @39
    @8
    eqid
    #
    @29
    eqid
    #
    linc0scn0
    syl2anc
    @10
    @34
    @8
    @29
    cfv
    #
    @13
    wne
    #
    vx
    @8
    cS
    @4
    @7
    @9
    simp3
    #
    @18
    @8
    wceq
    #
    @34
    @47
    wb
    @10
    @49
    @33
    @46
    @13
    @18
    @8
    @29
    fveq2
    neeq1d
    adantl
    @10
    @46
    @27
    @13
    @10
    @9
    @27
    cvv
    wcel
    @46
    @27
    wceq
    @48
    @10
    @1
    cur
    fvexd
    vs
    @8
    @28
    @27
    cS
    cvv
    @29
    @26
    @27
    @13
    iftrue
    @45
    fvmptg
    syl2anc
    @10
    @1
    crg
    wcel
    #
    @3
    wa
    #
    @27
    @13
    wne
    @4
    @7
    @51
    @9
    @0
    @50
    @3
    @1
    cM
    @37
    lmodring
    anim1i
    3ad2ant1
    @2
    @1
    @27
    @13
    @2
    eqid
    #
    @39
    @38
    ring1ne0
    syl
    eqnetrd
    rspcedvd
    @10
    @22
    @30
    @32
    @35
    w3a
    #
    vf
    @29
    @23
    @10
    @29
    @23
    wcel
    cS
    @2
    @29
    wf
    @10
    vs
    cS
    @28
    @2
    @29
    @10
    @28
    @2
    wcel
    #
    @25
    cS
    wcel
    @4
    @7
    @54
    @9
    @0
    @54
    @3
    @0
    @26
    @27
    @13
    @2
    @27
    @1
    @2
    cM
    @37
    @52
    @39
    lmod1cl
    @1
    @2
    cM
    @13
    @37
    @52
    @38
    lmod0cl
    ifcld
    adantr
    3ad2ant1
    adantr
    @45
    fmptd
    @10
    @2
    cS
    @29
    cvv
    @6
    @10
    @1
    cbs
    fvexd
    @43
    elmapd
    mpbird
    @12
    @29
    wceq
    #
    @22
    @53
    wb
    @10
    @55
    @14
    @30
    @17
    @32
    @21
    @35
    @12
    @29
    @13
    cfsupp
    breq1
    @55
    @16
    @31
    @8
    @12
    @29
    cS
    @15
    oveq1
    eqeq1d
    @55
    @20
    @34
    vx
    cS
    @55
    @19
    @33
    @13
    @18
    @12
    @29
    fveq1
    neeq1d
    rexbidv
    3anbi123d
    adantl
    rspcedv
    mp3and
    @10
    @0
    @7
    @11
    @24
    wb
    @42
    @43
    vx
    @5
    @1
    cS
    vf
    @2
    cM
    clmod
    @13
    @8
    @36
    @44
    @37
    @52
    @38
    islindeps
    syl2anc
    mpbird
end
