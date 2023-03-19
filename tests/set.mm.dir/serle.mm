include "cc0.mm"
include "caddc.mm"
include "cseq.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cvv.mm"
include "cv.mm"
include "cmpt.mm"
include "cfz.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "wceq.mm"
include "vex.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "resubcld.mm"
include "syl5eqel.mm"
include "subge0d.mm"
include "mpbird.mm"
include "syl6breqr.mm"
include "serge0.mm"
include "recnd.mm"
include "a1i.mm"
include "sersub.mm"
include "breqtrd.mm"
include "readdcl.mm"
include "adantl.mm"
include "seqcl.mm"
include "mpbid.mm"

theorem serle
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  assume serge0.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume serge0.2: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) e. RR )
  assume serle.3: |- ( ( ph /\ k e. ( M ... N ) ) -> ( G ` k ) e. RR )
  assume serle.4: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) <_ ( G ` k ) )

  disjoint F k
  disjoint G k
  disjoint M k
  disjoint N k
  disjoint k ph
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( seq M ( + , F ) ` N ) <_ ( seq M ( + , G ) ` N ) )

  proof
    wph
    cc0
    cN
    caddc
    cG
    cM
    cseq
    cfv
    #
    cN
    caddc
    cF
    cM
    cseq
    cfv
    #
    cmin
    co
    #
    cle
    wbr
    @1
    @0
    cle
    wbr
    wph
    cc0
    cN
    caddc
    vx
    cvv
    vx
    cv
    #
    cG
    cfv
    #
    @3
    cF
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    cM
    cseq
    cfv
    @2
    cle
    wph
    vk
    @7
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
    #
    @8
    @7
    cfv
    #
    @8
    cG
    cfv
    #
    @8
    cF
    cfv
    #
    cmin
    co
    #
    cr
    @8
    cvv
    wcel
    @10
    @13
    wceq
    #
    vk
    vex
    vx
    @8
    @6
    @13
    cvv
    @7
    @3
    @8
    wceq
    @4
    @11
    @5
    @12
    cmin
    @3
    @8
    cG
    fveq2
    @3
    @8
    cF
    fveq2
    oveq12d
    @7
    eqid
    @11
    @12
    cmin
    ovex
    fvmpt
    ax-mp
    #
    @9
    @11
    @12
    serle.3
    serge0.2
    resubcld
    syl5eqel
    @9
    cc0
    @13
    @10
    cle
    @9
    cc0
    @13
    cle
    wbr
    @12
    @11
    cle
    wbr
    serle.4
    @9
    @11
    @12
    serle.3
    serge0.2
    subge0d
    mpbird
    @15
    syl6breqr
    serge0
    wph
    vk
    cG
    cF
    @7
    cM
    cN
    serge0.1
    @9
    @11
    serle.3
    recnd
    @9
    @12
    serge0.2
    recnd
    @14
    @9
    @15
    a1i
    sersub
    breqtrd
    wph
    @0
    @1
    wph
    vk
    vx
    caddc
    cr
    cG
    cM
    cN
    serge0.1
    serle.3
    @8
    cr
    wcel
    @3
    cr
    wcel
    wa
    @8
    @3
    caddc
    co
    cr
    wcel
    wph
    @8
    @3
    readdcl
    adantl
    #
    seqcl
    wph
    vk
    vx
    caddc
    cr
    cF
    cM
    cN
    serge0.1
    serge0.2
    @16
    seqcl
    subge0d
    mpbid
end
