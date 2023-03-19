include "cn.mm"
include "citg1.mm"
include "cdm.mm"
include "cv.mm"
include "wf.mm"
include "c0p.mm"
include "cfv.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wa.mm"
include "wral.mm"
include "cmpt.mm"
include "cli.mm"
include "cr.mm"
include "w3a.mm"
include "wex.mm"
include "cof.mm"
include "citg2.mm"
include "wceq.mm"
include "mbfi1fseq.mm"
include "eeanv.mm"
include "cmbf.mm"
include "wcel.mm"
include "adantr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "simprl1.mm"
include "simprl2.mm"
include "simprl3.mm"
include "simprr1.mm"
include "simprr2.mm"
include "simprr3.mm"
include "itg2addlem.mm"
include "ex.mm"
include "exlimdvv.mm"
include "syl5bir.mm"
include "mp2and.mm"

theorem itg2add
  let wph: wff ph
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cQ: class Q
  assume itg2add.f1: |- ( ph -> F e. MblFn )
  assume itg2add.f2: |- ( ph -> F : RR --> ( 0 [,) +oo ) )
  assume itg2add.f3: |- ( ph -> ( S.2 ` F ) e. RR )
  assume itg2add.g1: |- ( ph -> G e. MblFn )
  assume itg2add.g2: |- ( ph -> G : RR --> ( 0 [,) +oo ) )
  assume itg2add.g3: |- ( ph -> ( S.2 ` G ) e. RR )


  assert |- ( ph -> ( S.2 ` ( F oF + G ) ) = ( ( S.2 ` F ) + ( S.2 ` G ) ) )

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
    c0p
    vn
    cv
    #
    @1
    cfv
    #
    cle
    cofr
    #
    wbr
    @4
    @3
    c1
    caddc
    co
    #
    @1
    cfv
    @5
    wbr
    wa
    vn
    cn
    wral
    #
    vn
    cn
    vx
    cv
    #
    @4
    cfv
    cmpt
    @8
    cF
    cfv
    cli
    wbr
    vx
    cr
    wral
    #
    w3a
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
    c0p
    @3
    @12
    cfv
    #
    @5
    wbr
    @14
    @6
    @12
    cfv
    @5
    wbr
    wa
    vn
    cn
    wral
    #
    vn
    cn
    @8
    @14
    cfv
    cmpt
    @8
    cG
    cfv
    cli
    wbr
    vx
    cr
    wral
    #
    w3a
    #
    vg
    wex
    #
    cF
    cG
    caddc
    cof
    co
    citg2
    cfv
    cF
    citg2
    cfv
    #
    cG
    citg2
    cfv
    #
    caddc
    co
    wceq
    #
    wph
    vx
    vf
    vn
    cF
    itg2add.f1
    itg2add.f2
    mbfi1fseq
    wph
    vx
    vg
    vn
    cG
    itg2add.g1
    itg2add.g2
    mbfi1fseq
    @11
    @18
    wa
    @10
    @17
    wa
    #
    vg
    wex
    vf
    wex
    wph
    @21
    @10
    @17
    vf
    vg
    eeanv
    wph
    @22
    @21
    vf
    vg
    wph
    @22
    @21
    wph
    @22
    wa
    vx
    @1
    @12
    vn
    cF
    cG
    wph
    cF
    cmbf
    wcel
    @22
    itg2add.f1
    adantr
    wph
    cr
    cc0
    cpnf
    cico
    co
    #
    cF
    wf
    @22
    itg2add.f2
    adantr
    wph
    @19
    cr
    wcel
    @22
    itg2add.f3
    adantr
    wph
    cG
    cmbf
    wcel
    @22
    itg2add.g1
    adantr
    wph
    cr
    @23
    cG
    wf
    @22
    itg2add.g2
    adantr
    wph
    @20
    cr
    wcel
    @22
    itg2add.g3
    adantr
    @2
    @7
    @9
    @17
    wph
    simprl1
    @2
    @7
    @9
    @17
    wph
    simprl2
    @2
    @7
    @9
    @17
    wph
    simprl3
    @13
    @15
    @16
    @10
    wph
    simprr1
    @13
    @15
    @16
    @10
    wph
    simprr2
    @13
    @15
    @16
    @10
    wph
    simprr3
    itg2addlem
    ex
    exlimdvv
    syl5bir
    mp2and
end
