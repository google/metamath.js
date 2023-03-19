include "csu.mm"
include "cv.mm"
include "ce.mm"
include "cfv.mm"
include "cn.mm"
include "wcel.mm"
include "cr.mm"
include "crab.mm"
include "cc.mm"
include "wss.mm"
include "ssrab2.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "a1i.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "elrab.mm"
include "simpll.mm"
include "simprl.mm"
include "readdcld.mm"
include "cmul.mm"
include "recnd.mm"
include "efadd.mm"
include "syl2anc.mm"
include "nnmulcl.mm"
include "ad2ant2l.mm"
include "eqeltrd.mm"
include "sylanbrc.mm"
include "syl2anb.mm"
include "adantl.mm"
include "cc0.mm"
include "c1.mm"
include "0re.mm"
include "1nn.mm"
include "ef0.mm"
include "syl6eq.mm"
include "mpbir2an.mm"
include "fsumcllem.mm"
include "simprbi.mm"
include "syl.mm"

theorem efnnfsumcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume efnnfsumcl.1: |- ( ph -> A e. Fin )
  assume efnnfsumcl.2: |- ( ( ph /\ k e. A ) -> B e. RR )
  assume efnnfsumcl.3: |- ( ( ph /\ k e. A ) -> ( exp ` B ) e. NN )

  disjoint A k
  disjoint k ph
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( exp ` sum_ k e. A B ) e. NN )

  proof
    wph
    cA
    cB
    vk
    csu
    #
    vx
    cv
    #
    ce
    cfv
    #
    cn
    wcel
    #
    vx
    cr
    crab
    #
    wcel
    #
    @0
    ce
    cfv
    #
    cn
    wcel
    #
    wph
    vy
    vz
    cA
    cB
    @4
    vk
    @4
    cc
    wss
    wph
    @4
    cr
    cc
    @3
    vx
    cr
    ssrab2
    ax-resscn
    sstri
    a1i
    vy
    cv
    #
    @4
    wcel
    #
    vz
    cv
    #
    @4
    wcel
    #
    wa
    @8
    @10
    caddc
    co
    #
    @4
    wcel
    #
    wph
    @9
    @8
    cr
    wcel
    #
    @8
    ce
    cfv
    #
    cn
    wcel
    #
    wa
    #
    @10
    cr
    wcel
    #
    @10
    ce
    cfv
    #
    cn
    wcel
    #
    wa
    #
    @13
    @11
    @3
    @16
    vx
    @8
    cr
    @1
    @8
    wceq
    @2
    @15
    cn
    @1
    @8
    ce
    fveq2
    eleq1d
    elrab
    @3
    @20
    vx
    @10
    cr
    @1
    @10
    wceq
    @2
    @19
    cn
    @1
    @10
    ce
    fveq2
    eleq1d
    elrab
    @17
    @21
    wa
    #
    @12
    cr
    wcel
    @12
    ce
    cfv
    #
    cn
    wcel
    #
    @13
    @22
    @8
    @10
    @14
    @16
    @21
    simpll
    #
    @17
    @18
    @20
    simprl
    #
    readdcld
    @22
    @23
    @15
    @19
    cmul
    co
    #
    cn
    @22
    @8
    cc
    wcel
    @10
    cc
    wcel
    @23
    @27
    wceq
    @22
    @8
    @25
    recnd
    @22
    @10
    @26
    recnd
    @8
    @10
    efadd
    syl2anc
    @16
    @20
    @27
    cn
    wcel
    @14
    @18
    @15
    @19
    nnmulcl
    ad2ant2l
    eqeltrd
    @3
    @24
    vx
    @12
    cr
    @1
    @12
    wceq
    @2
    @23
    cn
    @1
    @12
    ce
    fveq2
    eleq1d
    elrab
    sylanbrc
    syl2anb
    adantl
    efnnfsumcl.1
    wph
    vk
    cv
    cA
    wcel
    wa
    cB
    cr
    wcel
    cB
    ce
    cfv
    #
    cn
    wcel
    #
    cB
    @4
    wcel
    efnnfsumcl.2
    efnnfsumcl.3
    @3
    @29
    vx
    cB
    cr
    @1
    cB
    wceq
    @2
    @28
    cn
    @1
    cB
    ce
    fveq2
    eleq1d
    elrab
    sylanbrc
    cc0
    @4
    wcel
    #
    wph
    @30
    cc0
    cr
    wcel
    c1
    cn
    wcel
    #
    0re
    1nn
    @3
    @31
    vx
    cc0
    cr
    @1
    cc0
    wceq
    #
    @2
    c1
    cn
    @32
    @2
    cc0
    ce
    cfv
    c1
    @1
    cc0
    ce
    fveq2
    ef0
    syl6eq
    eleq1d
    elrab
    mpbir2an
    a1i
    fsumcllem
    @5
    @0
    cr
    wcel
    @7
    @3
    @7
    vx
    @0
    cr
    @1
    @0
    wceq
    @2
    @6
    cn
    @1
    @0
    ce
    fveq2
    eleq1d
    elrab
    simprbi
    syl
end
