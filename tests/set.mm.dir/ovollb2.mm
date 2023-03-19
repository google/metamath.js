include "cn.mm"
include "cle.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "wf.mm"
include "cicc.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "wa.mm"
include "covol.mm"
include "cfv.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wbr.mm"
include "cpnf.mm"
include "wceq.mm"
include "wcel.mm"
include "simpr.mm"
include "ovolficcss.mm"
include "adantr.mm"
include "sstrd.mm"
include "ovolcl.mm"
include "syl.mm"
include "pnfge.mm"
include "breqtrrd.mm"
include "wne.mm"
include "c0.mm"
include "wb.mm"
include "cc0.mm"
include "cico.mm"
include "co.mm"
include "cabs.mm"
include "cmin.mm"
include "eqid.mm"
include "ovolsf.mm"
include "frn.mm"
include "rge0ssre.mm"
include "syl6ss.mm"
include "cdm.mm"
include "c1.mm"
include "1nn.mm"
include "fdm.mm"
include "syl5eleqr.mm"
include "ne0i.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "sylib.mm"
include "supxrre2.mm"
include "syl2anc.mm"
include "biimpar.mm"
include "cv.mm"
include "caddc.mm"
include "crp.mm"
include "wral.mm"
include "c1st.mm"
include "c2.mm"
include "cdiv.mm"
include "cexp.mm"
include "c2nd.mm"
include "cop.mm"
include "cmpt.mm"
include "cseq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "opeq12d.mm"
include "cbvmptv.mm"
include "simplll.mm"
include "simpllr.mm"
include "simplr.mm"
include "ovollb2lem.mm"
include "ralrimiva.mm"
include "xralrple.mm"
include "sylan.mm"
include "mpbird.mm"
include "syldan.mm"
include "pm2.61dane.mm"

theorem ovollb2
  let cA: class A
  let cS: class S
  let cF: class F
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let cM: class M
  let cN: class N
  let vk: setvar k
  let cB: class B
  let wph: wff ph
  let cT: class T
  assume ovollb2.1: |- S = seq 1 ( + , ( ( abs o. - ) o. F ) )


  assert |- ( ( F : NN --> ( <_ i^i ( RR X. RR ) ) /\ A C_ U. ran ( [,] o. F ) ) -> ( vol* ` A ) <_ sup ( ran S , RR* , < ) )

  proof
    cn
    cle
    cr
    cr
    cxp
    cin
    cF
    wf
    #
    cA
    cicc
    cF
    ccom
    crn
    cuni
    #
    wss
    #
    wa
    #
    cA
    covol
    cfv
    #
    cS
    crn
    #
    cxr
    clt
    csup
    #
    cle
    wbr
    #
    @6
    cpnf
    @3
    @6
    cpnf
    wceq
    #
    wa
    #
    @4
    cpnf
    @6
    cle
    @9
    @4
    cxr
    wcel
    #
    @4
    cpnf
    cle
    wbr
    @3
    @10
    @8
    @3
    cA
    cr
    wss
    @10
    @3
    cA
    @1
    cr
    @0
    @2
    simpr
    @0
    @1
    cr
    wss
    @2
    cF
    ovolficcss
    adantr
    sstrd
    cA
    ovolcl
    syl
    #
    adantr
    @4
    pnfge
    syl
    @3
    @8
    simpr
    breqtrrd
    @3
    @6
    cpnf
    wne
    #
    @6
    cr
    wcel
    #
    @7
    @3
    @13
    @12
    @3
    @5
    cr
    wss
    @5
    c0
    wne
    #
    @13
    @12
    wb
    @3
    @5
    cc0
    cpnf
    cico
    co
    #
    cr
    @3
    cn
    @15
    cS
    wf
    #
    @5
    @15
    wss
    @0
    @16
    @2
    cS
    cF
    cabs
    cmin
    ccom
    #
    cF
    ccom
    #
    @18
    eqid
    ovollb2.1
    ovolsf
    adantr
    #
    cn
    @15
    cS
    frn
    syl
    rge0ssre
    syl6ss
    @3
    cS
    cdm
    #
    c0
    wne
    #
    @14
    @3
    c1
    @20
    wcel
    @21
    @3
    c1
    cn
    @20
    1nn
    @3
    @16
    @20
    cn
    wceq
    @19
    cn
    @15
    cS
    fdm
    syl
    syl5eleqr
    @20
    c1
    ne0i
    syl
    @20
    c0
    @5
    c0
    cS
    dm0rn0
    necon3bii
    sylib
    @5
    supxrre2
    syl2anc
    biimpar
    @3
    @13
    wa
    #
    @7
    @4
    @6
    vx
    cv
    #
    caddc
    co
    cle
    wbr
    #
    vx
    crp
    wral
    #
    @22
    @24
    vx
    crp
    @22
    @23
    crp
    wcel
    #
    wa
    cA
    @23
    cS
    caddc
    @17
    vm
    cn
    vm
    cv
    #
    cF
    cfv
    #
    c1st
    cfv
    #
    @23
    c2
    cdiv
    co
    #
    c2
    @27
    cexp
    co
    #
    cdiv
    co
    #
    cmin
    co
    #
    @28
    c2nd
    cfv
    #
    @32
    caddc
    co
    #
    cop
    #
    cmpt
    #
    ccom
    c1
    cseq
    #
    vn
    cF
    @37
    ovollb2.1
    vm
    vn
    cn
    @36
    vn
    cv
    #
    cF
    cfv
    #
    c1st
    cfv
    #
    @30
    c2
    @39
    cexp
    co
    #
    cdiv
    co
    #
    cmin
    co
    #
    @40
    c2nd
    cfv
    #
    @43
    caddc
    co
    #
    cop
    @27
    @39
    wceq
    #
    @33
    @44
    @35
    @46
    @47
    @29
    @41
    @32
    @43
    cmin
    @47
    @28
    @40
    c1st
    @27
    @39
    cF
    fveq2
    #
    fveq2d
    @47
    @31
    @42
    @30
    cdiv
    @27
    @39
    c2
    cexp
    oveq2
    oveq2d
    #
    oveq12d
    @47
    @34
    @45
    @32
    @43
    caddc
    @47
    @28
    @40
    c2nd
    @48
    fveq2d
    @49
    oveq12d
    opeq12d
    cbvmptv
    @38
    eqid
    @0
    @2
    @13
    @26
    simplll
    @0
    @2
    @13
    @26
    simpllr
    @22
    @26
    simpr
    @3
    @13
    @26
    simplr
    ovollb2lem
    ralrimiva
    @3
    @10
    @13
    @7
    @25
    wb
    @11
    vx
    @4
    @6
    xralrple
    sylan
    mpbird
    syldan
    pm2.61dane
end
