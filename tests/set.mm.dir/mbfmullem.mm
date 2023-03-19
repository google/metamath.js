include "cn.mm"
include "citg1.mm"
include "cdm.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "cmpt.mm"
include "cli.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "cmbf.mm"
include "wcel.mm"
include "mbfi1flim.mm"
include "eeanv.mm"
include "adantr.mm"
include "cr.mm"
include "simprll.mm"
include "simprlr.mm"
include "weq.mm"
include "fveq2.mm"
include "mpteq2dv.mm"
include "fveq1d.mm"
include "cbvmptv.mm"
include "syl6eq.mm"
include "breq12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "simprrl.mm"
include "simprrr.mm"
include "mbfmullem2.mm"
include "ex.mm"
include "exlimdvv.mm"
include "syl5bir.mm"
include "mp2and.mm"

theorem mbfmullem
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cQ: class Q
  assume mbfmul.1: |- ( ph -> F e. MblFn )
  assume mbfmul.2: |- ( ph -> G e. MblFn )
  assume mbfmul.3: |- ( ph -> F : A --> RR )
  assume mbfmul.4: |- ( ph -> G : A --> RR )


  assert |- ( ph -> ( F oF x. G ) e. MblFn )

  proof
    wph
    cn
    citg1
    cdm
    #
    vf
    cv
    #
    wf
    #
    vn
    cn
    vy
    cv
    #
    vn
    cv
    #
    @1
    cfv
    #
    cfv
    #
    cmpt
    #
    @3
    cF
    cfv
    #
    cli
    wbr
    #
    vy
    cA
    wral
    #
    wa
    #
    vf
    wex
    #
    cn
    @0
    vg
    cv
    #
    wf
    #
    vn
    cn
    @3
    @4
    @13
    cfv
    #
    cfv
    #
    cmpt
    #
    @3
    cG
    cfv
    #
    cli
    wbr
    #
    vy
    cA
    wral
    #
    wa
    #
    vg
    wex
    #
    cF
    cG
    cmul
    cof
    co
    cmbf
    wcel
    #
    wph
    vy
    cA
    vf
    vn
    cF
    mbfmul.1
    mbfmul.3
    mbfi1flim
    wph
    vy
    cA
    vg
    vn
    cG
    mbfmul.2
    mbfmul.4
    mbfi1flim
    @12
    @22
    wa
    @11
    @21
    wa
    #
    vg
    wex
    vf
    wex
    wph
    @23
    @11
    @21
    vf
    vg
    eeanv
    wph
    @24
    @23
    vf
    vg
    wph
    @24
    @23
    wph
    @24
    wa
    #
    vx
    cA
    @1
    @13
    vm
    cF
    cG
    wph
    cF
    cmbf
    wcel
    @24
    mbfmul.1
    adantr
    wph
    cG
    cmbf
    wcel
    @24
    mbfmul.2
    adantr
    wph
    cA
    cr
    cF
    wf
    @24
    mbfmul.3
    adantr
    wph
    cA
    cr
    cG
    wf
    @24
    mbfmul.4
    adantr
    wph
    @2
    @10
    @21
    simprll
    @25
    @10
    vx
    cv
    #
    cA
    wcel
    #
    vm
    cn
    @26
    vm
    cv
    #
    @1
    cfv
    #
    cfv
    #
    cmpt
    #
    @26
    cF
    cfv
    #
    cli
    wbr
    #
    wph
    @2
    @10
    @21
    simprlr
    @9
    @33
    vy
    @26
    cA
    vy
    vx
    weq
    #
    @7
    @31
    @8
    @32
    cli
    @34
    @7
    vn
    cn
    @26
    @5
    cfv
    #
    cmpt
    @31
    @34
    vn
    cn
    @6
    @35
    @3
    @26
    @5
    fveq2
    mpteq2dv
    vn
    vm
    cn
    @35
    @30
    vn
    vm
    weq
    #
    @26
    @5
    @29
    @4
    @28
    @1
    fveq2
    fveq1d
    cbvmptv
    syl6eq
    @3
    @26
    cF
    fveq2
    breq12d
    rspccva
    sylan
    wph
    @11
    @14
    @20
    simprrl
    @25
    @20
    @27
    vm
    cn
    @26
    @28
    @13
    cfv
    #
    cfv
    #
    cmpt
    #
    @26
    cG
    cfv
    #
    cli
    wbr
    #
    wph
    @11
    @14
    @20
    simprrr
    @19
    @41
    vy
    @26
    cA
    @34
    @17
    @39
    @18
    @40
    cli
    @34
    @17
    vn
    cn
    @26
    @15
    cfv
    #
    cmpt
    @39
    @34
    vn
    cn
    @16
    @42
    @3
    @26
    @15
    fveq2
    mpteq2dv
    vn
    vm
    cn
    @42
    @38
    @36
    @26
    @15
    @37
    @4
    @28
    @13
    fveq2
    fveq1d
    cbvmptv
    syl6eq
    @3
    @26
    cG
    fveq2
    breq12d
    rspccva
    sylan
    mbfmullem2
    ex
    exlimdvv
    syl5bir
    mp2and
end
