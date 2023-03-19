include "covol.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "caddc.mm"
include "crp.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cioo.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "cabs.mm"
include "cmin.mm"
include "c1.mm"
include "cseq.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cmul.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "cn.mm"
include "cmap.mm"
include "wrex.mm"
include "adantr.mm"
include "rpmulcl.mm"
include "sylan.mm"
include "eqid.mm"
include "ovolgelb.mm"
include "syl3anc.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "cmpt.mm"
include "ad2antrr.mm"
include "crab.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "opeq12d.mm"
include "cbvmptv.mm"
include "wf.mm"
include "elmapi.mm"
include "ad2antrl.mm"
include "simprrl.mm"
include "simplr.mm"
include "simprrr.mm"
include "ovolscalem1.mm"
include "rexlimddv.mm"
include "ralrimiva.mm"
include "wb.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "ovolcl.mm"
include "syl.mm"
include "rerpdivcld.mm"
include "xralrple.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem ovolscalem2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vy: setvar y
  let cF: class F
  let cG: class G
  let cR: class R
  let vm: setvar m
  let cS: class S
  assume ovolsca.1: |- ( ph -> A C_ RR )
  assume ovolsca.2: |- ( ph -> C e. RR+ )
  assume ovolsca.3: |- ( ph -> B = { x e. RR | ( C x. x ) e. A } )
  assume ovolsca.4: |- ( ph -> ( vol* ` A ) e. RR )

  disjoint A x
  disjoint C x
  disjoint f k
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A y
  disjoint B f
  disjoint B n
  disjoint B y
  disjoint F n
  disjoint F x
  disjoint G k
  disjoint G n
  disjoint G y
  disjoint R k
  disjoint R x
  disjoint R y
  disjoint f m
  disjoint C f
  disjoint k m
  disjoint C k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint C m
  disjoint C n
  disjoint C y
  disjoint f ph
  disjoint k ph
  disjoint n ph
  disjoint ph y
  disjoint S k
  disjoint S x
  assert |- ( ph -> ( vol* ` B ) <_ ( ( vol* ` A ) / C ) )

  proof
    wph
    cB
    covol
    cfv
    #
    cA
    covol
    cfv
    #
    cC
    cdiv
    co
    #
    cle
    wbr
    #
    @0
    @2
    vy
    cv
    #
    caddc
    co
    cle
    wbr
    #
    vy
    crp
    wral
    #
    wph
    @5
    vy
    crp
    wph
    @4
    crp
    wcel
    #
    wa
    #
    cA
    cioo
    vf
    cv
    #
    ccom
    crn
    cuni
    wss
    #
    caddc
    cabs
    cmin
    ccom
    @9
    ccom
    c1
    cseq
    #
    crn
    cxr
    clt
    csup
    @1
    cC
    @4
    cmul
    co
    #
    caddc
    co
    cle
    wbr
    #
    wa
    #
    @5
    vf
    cle
    cr
    cr
    cxp
    cin
    #
    cn
    cmap
    co
    #
    @8
    cA
    cr
    wss
    #
    @1
    cr
    wcel
    #
    @12
    crp
    wcel
    #
    @14
    vf
    @16
    wrex
    wph
    @17
    @7
    ovolsca.1
    adantr
    wph
    @18
    @7
    ovolsca.4
    adantr
    wph
    cC
    crp
    wcel
    #
    @7
    @19
    ovolsca.2
    cC
    @4
    rpmulcl
    sylan
    cA
    @12
    @11
    vf
    @11
    eqid
    #
    ovolgelb
    syl3anc
    @8
    @9
    @16
    wcel
    #
    @14
    wa
    #
    wa
    vx
    cA
    cB
    cC
    @4
    @11
    vn
    @9
    vm
    cn
    vm
    cv
    #
    @9
    cfv
    #
    c1st
    cfv
    #
    cC
    cdiv
    co
    #
    @25
    c2nd
    cfv
    #
    cC
    cdiv
    co
    #
    cop
    #
    cmpt
    wph
    @17
    @7
    @23
    ovolsca.1
    ad2antrr
    wph
    @20
    @7
    @23
    ovolsca.2
    ad2antrr
    wph
    cB
    cC
    vx
    cv
    cmul
    co
    cA
    wcel
    #
    vx
    cr
    crab
    #
    wceq
    @7
    @23
    ovolsca.3
    ad2antrr
    wph
    @18
    @7
    @23
    ovolsca.4
    ad2antrr
    @21
    vm
    vn
    cn
    @30
    vn
    cv
    #
    @9
    cfv
    #
    c1st
    cfv
    #
    cC
    cdiv
    co
    #
    @34
    c2nd
    cfv
    #
    cC
    cdiv
    co
    #
    cop
    @24
    @33
    wceq
    #
    @27
    @36
    @29
    @38
    @39
    @26
    @35
    cC
    cdiv
    @39
    @25
    @34
    c1st
    @24
    @33
    @9
    fveq2
    #
    fveq2d
    oveq1d
    @39
    @28
    @37
    cC
    cdiv
    @39
    @25
    @34
    c2nd
    @40
    fveq2d
    oveq1d
    opeq12d
    cbvmptv
    @22
    cn
    @15
    @9
    wf
    @8
    @14
    @9
    @15
    cn
    elmapi
    ad2antrl
    @8
    @22
    @10
    @13
    simprrl
    wph
    @7
    @23
    simplr
    @8
    @22
    @10
    @13
    simprrr
    ovolscalem1
    rexlimddv
    ralrimiva
    wph
    @0
    cxr
    wcel
    #
    @2
    cr
    wcel
    @3
    @6
    wb
    wph
    cB
    cr
    wss
    @41
    wph
    cB
    @32
    cr
    ovolsca.3
    @31
    vx
    cr
    ssrab2
    syl6eqss
    cB
    ovolcl
    syl
    wph
    @1
    cC
    ovolsca.4
    ovolsca.2
    rerpdivcld
    vy
    @0
    @2
    xralrple
    syl2anc
    mpbird
end
