include "cmul.mm"
include "cseq.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "cmpt.mm"
include "wcel.mm"
include "wceq.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "prodfrec.mm"
include "cc.mm"
include "wa.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvarv.mm"
include "cc0.mm"
include "wne.mm"
include "neeq1d.mm"
include "reccld.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "divrecd.mm"
include "3eqtr4d.mm"
include "prodfmul.mm"
include "mulcl.mm"
include "seqcl.mm"
include "prodfn0.mm"

theorem prodfdiv
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vn: setvar n
  assume prodfdiv.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume prodfdiv.2: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) e. CC )
  assume prodfdiv.3: |- ( ( ph /\ k e. ( M ... N ) ) -> ( G ` k ) e. CC )
  assume prodfdiv.4: |- ( ( ph /\ k e. ( M ... N ) ) -> ( G ` k ) =/= 0 )
  assume prodfdiv.5: |- ( ( ph /\ k e. ( M ... N ) ) -> ( H ` k ) = ( ( F ` k ) / ( G ` k ) ) )

  disjoint F k
  disjoint G k
  disjoint H k
  disjoint k ph
  disjoint M k
  disjoint N k
  disjoint F x
  disjoint G n
  disjoint G x
  disjoint k n
  disjoint k x
  disjoint M n
  disjoint M x
  disjoint N n
  disjoint n ph
  disjoint ph x
  assert |- ( ph -> ( seq M ( x. , H ) ` N ) = ( ( seq M ( x. , F ) ` N ) / ( seq M ( x. , G ) ` N ) ) )

  proof
    wph
    cN
    cmul
    cF
    cM
    cseq
    cfv
    #
    cN
    cmul
    vn
    cM
    cN
    cfz
    co
    #
    c1
    vn
    cv
    #
    cG
    cfv
    #
    cdiv
    co
    #
    cmpt
    #
    cM
    cseq
    cfv
    #
    cmul
    co
    @0
    c1
    cN
    cmul
    cG
    cM
    cseq
    cfv
    #
    cdiv
    co
    #
    cmul
    co
    cN
    cmul
    cH
    cM
    cseq
    cfv
    @0
    @7
    cdiv
    co
    wph
    @6
    @8
    @0
    cmul
    wph
    vk
    cG
    @5
    cM
    cN
    prodfdiv.1
    prodfdiv.3
    prodfdiv.4
    vk
    cv
    #
    @1
    wcel
    #
    @9
    @5
    cfv
    #
    c1
    @9
    cG
    cfv
    #
    cdiv
    co
    #
    wceq
    wph
    vn
    @9
    @4
    @13
    @1
    @5
    vn
    vk
    weq
    @3
    @12
    c1
    cdiv
    @2
    @9
    cG
    fveq2
    oveq2d
    @5
    eqid
    #
    c1
    @12
    cdiv
    ovex
    fvmpt
    adantl
    #
    prodfrec
    oveq2d
    wph
    vk
    cF
    @5
    cH
    cM
    cN
    prodfdiv.1
    prodfdiv.2
    wph
    @1
    cc
    @9
    @5
    wph
    vn
    @1
    @4
    cc
    @5
    wph
    @2
    @1
    wcel
    #
    wa
    #
    @3
    wph
    @10
    wa
    #
    @12
    cc
    wcel
    #
    wi
    @17
    @3
    cc
    wcel
    #
    wi
    vk
    vn
    vk
    vn
    weq
    #
    @18
    @17
    @19
    @20
    @21
    @10
    @16
    wph
    @9
    @2
    @1
    eleq1
    anbi2d
    #
    @21
    @12
    @3
    cc
    @9
    @2
    cG
    fveq2
    #
    eleq1d
    imbi12d
    prodfdiv.3
    chvarv
    @18
    @12
    cc0
    wne
    #
    wi
    @17
    @3
    cc0
    wne
    #
    wi
    vk
    vn
    @21
    @18
    @17
    @24
    @25
    @22
    @21
    @12
    @3
    cc0
    @23
    neeq1d
    imbi12d
    prodfdiv.4
    chvarv
    reccld
    @14
    fmptd
    ffvelrnda
    @18
    @9
    cF
    cfv
    #
    @12
    cdiv
    co
    @26
    @13
    cmul
    co
    @9
    cH
    cfv
    @26
    @11
    cmul
    co
    @18
    @26
    @12
    prodfdiv.2
    prodfdiv.3
    prodfdiv.4
    divrecd
    prodfdiv.5
    @18
    @11
    @13
    @26
    cmul
    @15
    oveq2d
    3eqtr4d
    prodfmul
    wph
    @0
    @7
    wph
    vk
    vx
    cmul
    cc
    cF
    cM
    cN
    prodfdiv.1
    prodfdiv.2
    @9
    cc
    wcel
    vx
    cv
    #
    cc
    wcel
    wa
    @9
    @27
    cmul
    co
    cc
    wcel
    wph
    @9
    @27
    mulcl
    adantl
    #
    seqcl
    wph
    vk
    vx
    cmul
    cc
    cG
    cM
    cN
    prodfdiv.1
    prodfdiv.3
    @28
    seqcl
    wph
    vk
    cG
    cM
    cN
    prodfdiv.1
    prodfdiv.3
    prodfdiv.4
    prodfn0
    divrecd
    3eqtr4d
end
