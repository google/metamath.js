include "c1.mm"
include "cc0.mm"
include "caddc.mm"
include "co.mm"
include "cli.mm"
include "cn.mm"
include "cmpt.mm"
include "cv.mm"
include "cmul.mm"
include "cdiv.mm"
include "cvv.mm"
include "nnuz.mm"
include "1zzd.mm"
include "wcel.mm"
include "nnex.mm"
include "mptex.mm"
include "a1i.mm"
include "1cnd.mm"
include "cfv.mm"
include "wceq.mm"
include "cc.mm"
include "eqidd.mm"
include "wa.mm"
include "id.mm"
include "fvmptd.mm"
include "adantl.mm"
include "climconst.mm"
include "eqeltri.mm"
include "adantr.mm"
include "nncn.mm"
include "wne.mm"
include "nnne0.mm"
include "divdiv1d.mm"
include "mpteq2dva.mm"
include "wbr.mm"
include "divcld.mm"
include "divcnv.mm"
include "syl.mm"
include "eqbrtrrd.mm"
include "wf.mm"
include "eqid.mm"
include "fmpti.mm"
include "ffvelrnda.mm"
include "mulcld.mm"
include "mulne0d.mm"
include "fmptd.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "simpr.mm"
include "nncnd.mm"
include "addcld.mm"
include "nnne0d.mm"
include "divdird.mm"
include "dividd.mm"
include "eqtrd.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "climadd.mm"
include "1p0e1.mm"
include "syl6breq.mm"

theorem clim1fr1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vn: setvar n
  let cF: class F
  let vk: setvar k
  assume clim1fr1.1: |- F = ( n e. NN |-> ( ( ( A x. n ) + B ) / ( A x. n ) ) )
  assume clim1fr1.2: |- ( ph -> A e. CC )
  assume clim1fr1.3: |- ( ph -> A =/= 0 )
  assume clim1fr1.4: |- ( ph -> B e. CC )

  disjoint n ph
  disjoint A n
  disjoint B n
  disjoint k n
  disjoint k ph
  disjoint A k
  disjoint B k
  disjoint F k
  assert |- ( ph -> F ~~> 1 )

  proof
    wph
    cF
    c1
    cc0
    caddc
    co
    c1
    cli
    wph
    c1
    cc0
    vk
    vn
    cn
    c1
    cmpt
    #
    vn
    cn
    cB
    cA
    vn
    cv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cmpt
    #
    cF
    c1
    cvv
    cn
    nnuz
    wph
    1zzd
    #
    wph
    c1
    vk
    @0
    c1
    cvv
    cn
    nnuz
    @5
    @0
    cvv
    wcel
    wph
    vn
    cn
    c1
    nnex
    mptex
    a1i
    wph
    1cnd
    vk
    cv
    #
    cn
    wcel
    #
    @6
    @0
    cfv
    #
    c1
    wceq
    wph
    @7
    vn
    @6
    c1
    c1
    cn
    @0
    cc
    @7
    @0
    eqidd
    @7
    @1
    @6
    wceq
    #
    wa
    c1
    eqidd
    @7
    id
    @7
    1cnd
    fvmptd
    adantl
    #
    climconst
    cF
    cvv
    wcel
    wph
    cF
    vn
    cn
    @2
    cB
    caddc
    co
    #
    @2
    cdiv
    co
    #
    cmpt
    #
    cvv
    clim1fr1.1
    vn
    cn
    @12
    nnex
    mptex
    eqeltri
    a1i
    wph
    vn
    cn
    cB
    cA
    cdiv
    co
    #
    @1
    cdiv
    co
    #
    cmpt
    #
    @4
    cc0
    cli
    wph
    vn
    cn
    @15
    @3
    wph
    @1
    cn
    wcel
    #
    wa
    #
    cB
    cA
    @1
    wph
    cB
    cc
    wcel
    #
    @17
    clim1fr1.4
    adantr
    #
    wph
    cA
    cc
    wcel
    #
    @17
    clim1fr1.2
    adantr
    #
    @17
    @1
    cc
    wcel
    wph
    @1
    nncn
    adantl
    #
    wph
    cA
    cc0
    wne
    #
    @17
    clim1fr1.3
    adantr
    #
    @17
    @1
    cc0
    wne
    wph
    @1
    nnne0
    adantl
    #
    divdiv1d
    mpteq2dva
    wph
    @14
    cc
    wcel
    @16
    cc0
    cli
    wbr
    wph
    cB
    cA
    clim1fr1.4
    clim1fr1.2
    clim1fr1.3
    divcld
    @14
    vn
    divcnv
    syl
    eqbrtrrd
    wph
    cn
    cc
    @6
    @0
    cn
    cc
    @0
    wf
    wph
    vn
    cn
    cc
    c1
    @0
    @0
    eqid
    @17
    1cnd
    fmpti
    a1i
    ffvelrnda
    wph
    cn
    cc
    @6
    @4
    wph
    vn
    cn
    @3
    cc
    @4
    @18
    cB
    @2
    @20
    @18
    cA
    @1
    @22
    @23
    mulcld
    @18
    cA
    @1
    @22
    @23
    @25
    @26
    mulne0d
    divcld
    @4
    eqid
    fmptd
    ffvelrnda
    wph
    @7
    wa
    #
    @6
    cF
    cfv
    cA
    @6
    cmul
    co
    #
    cB
    caddc
    co
    #
    @28
    cdiv
    co
    #
    c1
    cB
    @28
    cdiv
    co
    #
    caddc
    co
    #
    @8
    @6
    @4
    cfv
    #
    caddc
    co
    @27
    vn
    @6
    @12
    @30
    cn
    cF
    cc
    cF
    @13
    wceq
    @27
    clim1fr1.1
    a1i
    @9
    @12
    @30
    wceq
    @27
    @9
    @11
    @29
    @2
    @28
    cdiv
    @9
    @2
    @28
    cB
    caddc
    @1
    @6
    cA
    cmul
    oveq2
    #
    oveq1d
    @34
    oveq12d
    adantl
    wph
    @7
    simpr
    #
    @27
    @29
    @28
    @27
    @28
    cB
    @27
    cA
    @6
    wph
    @21
    @7
    clim1fr1.2
    adantr
    #
    @27
    @6
    @35
    nncnd
    #
    mulcld
    #
    wph
    @19
    @7
    clim1fr1.4
    adantr
    #
    addcld
    @38
    @27
    cA
    @6
    @36
    @37
    wph
    @24
    @7
    clim1fr1.3
    adantr
    @27
    @6
    @35
    nnne0d
    mulne0d
    #
    divcld
    fvmptd
    @27
    @30
    @28
    @28
    cdiv
    co
    #
    @31
    caddc
    co
    @32
    @27
    @28
    cB
    @28
    @38
    @39
    @38
    @40
    divdird
    @27
    @41
    c1
    @31
    caddc
    @27
    @28
    @38
    @40
    dividd
    oveq1d
    eqtrd
    @27
    c1
    @8
    @31
    @33
    caddc
    @27
    @8
    c1
    @10
    eqcomd
    @27
    @33
    @31
    @27
    vn
    @6
    @3
    @31
    cn
    @4
    cc
    @27
    @4
    eqidd
    @27
    @9
    wa
    #
    @2
    @28
    cB
    cdiv
    @42
    @1
    @6
    cA
    cmul
    @27
    @9
    simpr
    oveq2d
    oveq2d
    @35
    @27
    cB
    @28
    @39
    @38
    @40
    divcld
    fvmptd
    eqcomd
    oveq12d
    3eqtrd
    climadd
    1p0e1
    syl6breq
end
