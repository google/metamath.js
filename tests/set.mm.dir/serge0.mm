include "caddc.mm"
include "cseq.mm"
include "cfv.mm"
include "cc0.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "crab.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "breq2.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "readdcl.mm"
include "ad2ant2r.mm"
include "addge0.mm"
include "an4s.mm"
include "syl2anb.mm"
include "adantl.mm"
include "seqcl.mm"
include "simprbi.mm"
include "syl.mm"

theorem serge0
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  assume serge0.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume serge0.2: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) e. RR )
  assume serge0.3: |- ( ( ph /\ k e. ( M ... N ) ) -> 0 <_ ( F ` k ) )

  disjoint F k
  disjoint M k
  disjoint N k
  disjoint k ph
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G k
  disjoint G x
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> 0 <_ ( seq M ( + , F ) ` N ) )

  proof
    wph
    cN
    caddc
    cF
    cM
    cseq
    cfv
    #
    cc0
    vx
    cv
    #
    cle
    wbr
    #
    vx
    cr
    crab
    #
    wcel
    #
    cc0
    @0
    cle
    wbr
    #
    wph
    vk
    vy
    caddc
    @3
    cF
    cM
    cN
    serge0.1
    wph
    vk
    cv
    #
    cM
    cN
    cfz
    co
    wcel
    wa
    @6
    cF
    cfv
    #
    cr
    wcel
    cc0
    @7
    cle
    wbr
    #
    @7
    @3
    wcel
    serge0.2
    serge0.3
    @2
    @8
    vx
    @7
    cr
    @1
    @7
    cc0
    cle
    breq2
    elrab
    sylanbrc
    @6
    @3
    wcel
    #
    vy
    cv
    #
    @3
    wcel
    #
    wa
    @6
    @10
    caddc
    co
    #
    @3
    wcel
    #
    wph
    @9
    @6
    cr
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    wa
    #
    @10
    cr
    wcel
    #
    cc0
    @10
    cle
    wbr
    #
    wa
    #
    @13
    @11
    @2
    @15
    vx
    @6
    cr
    @1
    @6
    cc0
    cle
    breq2
    elrab
    @2
    @18
    vx
    @10
    cr
    @1
    @10
    cc0
    cle
    breq2
    elrab
    @16
    @19
    wa
    @12
    cr
    wcel
    #
    cc0
    @12
    cle
    wbr
    #
    @13
    @14
    @17
    @20
    @15
    @18
    @6
    @10
    readdcl
    ad2ant2r
    @14
    @17
    @15
    @18
    @21
    @6
    @10
    addge0
    an4s
    @2
    @21
    vx
    @12
    cr
    @1
    @12
    cc0
    cle
    breq2
    elrab
    sylanbrc
    syl2anb
    adantl
    seqcl
    @4
    @0
    cr
    wcel
    @5
    @2
    @5
    vx
    @0
    cr
    @1
    @0
    cc0
    cle
    breq2
    elrab
    simprbi
    syl
end
