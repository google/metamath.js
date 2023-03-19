include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cseq.mm"
include "cfv.mm"
include "wceq.mm"
include "cuz.mm"
include "eluzfz2.mm"
include "syl.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "wral.mm"
include "eluzfz1.mm"
include "ralrimiva.mm"
include "rspcv.mm"
include "sylc.mm"
include "cz.mm"
include "eluzel2.mm"
include "seq1.mm"
include "3eqtr4d.mm"
include "a1i.mm"
include "cfzo.mm"
include "wa.mm"
include "oveq1.mm"
include "elfzouz.mm"
include "adantl.mm"
include "seqp1.mm"
include "fzofzp1.mm"
include "adantr.mm"
include "oveq2d.mm"
include "3eqtr4rd.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "a2d.mm"
include "fzind2.mm"
include "mpcom.mm"

theorem seqcaopr3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let cQ: class Q
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let vz: setvar z
  assume seqcaopr3.1: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x .+ y ) e. S )
  assume seqcaopr3.2: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x Q y ) e. S )
  assume seqcaopr3.3: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume seqcaopr3.4: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) e. S )
  assume seqcaopr3.5: |- ( ( ph /\ k e. ( M ... N ) ) -> ( G ` k ) e. S )
  assume seqcaopr3.6: |- ( ( ph /\ k e. ( M ... N ) ) -> ( H ` k ) = ( ( F ` k ) Q ( G ` k ) ) )
  assume seqcaopr3.7: |- ( ( ph /\ n e. ( M ..^ N ) ) -> ( ( ( seq M ( .+ , F ) ` n ) Q ( seq M ( .+ , G ) ` n ) ) .+ ( ( F ` ( n + 1 ) ) Q ( G ` ( n + 1 ) ) ) ) = ( ( ( seq M ( .+ , F ) ` n ) .+ ( F ` ( n + 1 ) ) ) Q ( ( seq M ( .+ , G ) ` n ) .+ ( G ` ( n + 1 ) ) ) ) )

  disjoint k n
  disjoint k x
  disjoint k y
  disjoint F k
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint H k
  disjoint H n
  disjoint N k
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint k ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint G k
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint M k
  disjoint M n
  disjoint M x
  disjoint M y
  disjoint Q k
  disjoint Q n
  disjoint Q x
  disjoint Q y
  disjoint .+ n
  disjoint .+ x
  disjoint .+ y
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint k z
  disjoint n z
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint H z
  disjoint N z
  disjoint ph z
  disjoint G z
  disjoint M z
  disjoint Q z
  disjoint .+ z
  disjoint S z
  assert |- ( ph -> ( seq M ( .+ , H ) ` N ) = ( ( seq M ( .+ , F ) ` N ) Q ( seq M ( .+ , G ) ` N ) ) )

  proof
    cN
    cM
    cN
    cfz
    co
    #
    wcel
    #
    wph
    cN
    c.pl
    cH
    cM
    cseq
    #
    cfv
    #
    cN
    c.pl
    cF
    cM
    cseq
    #
    cfv
    #
    cN
    c.pl
    cG
    cM
    cseq
    #
    cfv
    #
    cQ
    co
    #
    wceq
    #
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    @1
    seqcaopr3.3
    cM
    cN
    eluzfz2
    syl
    wph
    vz
    cv
    #
    @2
    cfv
    #
    @12
    @4
    cfv
    #
    @12
    @6
    cfv
    #
    cQ
    co
    #
    wceq
    #
    wi
    wph
    cM
    @2
    cfv
    #
    cM
    @4
    cfv
    #
    cM
    @6
    cfv
    #
    cQ
    co
    #
    wceq
    #
    wi
    #
    wph
    vn
    cv
    #
    @2
    cfv
    #
    @24
    @4
    cfv
    #
    @24
    @6
    cfv
    #
    cQ
    co
    #
    wceq
    #
    wi
    wph
    @24
    c1
    caddc
    co
    #
    @2
    cfv
    #
    @30
    @4
    cfv
    #
    @30
    @6
    cfv
    #
    cQ
    co
    #
    wceq
    #
    wi
    wph
    @9
    wi
    vz
    vn
    cN
    cM
    cN
    @12
    cM
    wceq
    #
    @17
    @22
    wph
    @36
    @13
    @18
    @16
    @21
    @12
    cM
    @2
    fveq2
    @36
    @14
    @19
    @15
    @20
    cQ
    @12
    cM
    @4
    fveq2
    @12
    cM
    @6
    fveq2
    oveq12d
    eqeq12d
    imbi2d
    @12
    @24
    wceq
    #
    @17
    @29
    wph
    @37
    @13
    @25
    @16
    @28
    @12
    @24
    @2
    fveq2
    @37
    @14
    @26
    @15
    @27
    cQ
    @12
    @24
    @4
    fveq2
    @12
    @24
    @6
    fveq2
    oveq12d
    eqeq12d
    imbi2d
    @12
    @30
    wceq
    #
    @17
    @35
    wph
    @38
    @13
    @31
    @16
    @34
    @12
    @30
    @2
    fveq2
    @38
    @14
    @32
    @15
    @33
    cQ
    @12
    @30
    @4
    fveq2
    @12
    @30
    @6
    fveq2
    oveq12d
    eqeq12d
    imbi2d
    @12
    cN
    wceq
    #
    @17
    @9
    wph
    @39
    @13
    @3
    @16
    @8
    @12
    cN
    @2
    fveq2
    @39
    @14
    @5
    @15
    @7
    cQ
    @12
    cN
    @4
    fveq2
    @12
    cN
    @6
    fveq2
    oveq12d
    eqeq12d
    imbi2d
    @23
    @11
    wph
    cM
    cH
    cfv
    #
    cM
    cF
    cfv
    #
    cM
    cG
    cfv
    #
    cQ
    co
    #
    @18
    @21
    wph
    cM
    @0
    wcel
    #
    vk
    cv
    #
    cH
    cfv
    #
    @45
    cF
    cfv
    #
    @45
    cG
    cfv
    #
    cQ
    co
    #
    wceq
    #
    vk
    @0
    wral
    #
    @40
    @43
    wceq
    #
    wph
    @11
    @44
    seqcaopr3.3
    cM
    cN
    eluzfz1
    syl
    wph
    @50
    vk
    @0
    seqcaopr3.6
    ralrimiva
    #
    @50
    @52
    vk
    cM
    @0
    @45
    cM
    wceq
    #
    @46
    @40
    @49
    @43
    @45
    cM
    cH
    fveq2
    @54
    @47
    @41
    @48
    @42
    cQ
    @45
    cM
    cF
    fveq2
    @45
    cM
    cG
    fveq2
    oveq12d
    eqeq12d
    rspcv
    sylc
    wph
    cM
    cz
    wcel
    #
    @18
    @40
    wceq
    wph
    @11
    @55
    seqcaopr3.3
    cM
    cN
    eluzel2
    syl
    #
    c.pl
    cH
    cM
    seq1
    syl
    wph
    @55
    @21
    @43
    wceq
    @56
    @55
    @19
    @41
    @20
    @42
    cQ
    c.pl
    cF
    cM
    seq1
    c.pl
    cG
    cM
    seq1
    oveq12d
    syl
    3eqtr4d
    a1i
    @24
    cM
    cN
    cfzo
    co
    wcel
    #
    wph
    @29
    @35
    wph
    @57
    @29
    @35
    wi
    @29
    @35
    wph
    @57
    wa
    #
    @25
    @30
    cH
    cfv
    #
    c.pl
    co
    #
    @28
    @59
    c.pl
    co
    #
    wceq
    @25
    @28
    @59
    c.pl
    oveq1
    @58
    @31
    @60
    @34
    @61
    @58
    @24
    @10
    wcel
    #
    @31
    @60
    wceq
    @57
    @62
    wph
    @24
    cM
    cN
    elfzouz
    adantl
    #
    c.pl
    cH
    cM
    @24
    seqp1
    syl
    @58
    @28
    @30
    cF
    cfv
    #
    @30
    cG
    cfv
    #
    cQ
    co
    #
    c.pl
    co
    @26
    @64
    c.pl
    co
    #
    @27
    @65
    c.pl
    co
    #
    cQ
    co
    #
    @61
    @34
    seqcaopr3.7
    @58
    @59
    @66
    @28
    c.pl
    @58
    @30
    @0
    wcel
    #
    @51
    @59
    @66
    wceq
    #
    @57
    @70
    wph
    cM
    cN
    @24
    fzofzp1
    adantl
    wph
    @51
    @57
    @53
    adantr
    @50
    @71
    vk
    @30
    @0
    @45
    @30
    wceq
    #
    @46
    @59
    @49
    @66
    @45
    @30
    cH
    fveq2
    @72
    @47
    @64
    @48
    @65
    cQ
    @45
    @30
    cF
    fveq2
    @45
    @30
    cG
    fveq2
    oveq12d
    eqeq12d
    rspcv
    sylc
    oveq2d
    @58
    @62
    @34
    @69
    wceq
    @63
    @62
    @32
    @67
    @33
    @68
    cQ
    c.pl
    cF
    cM
    @24
    seqp1
    c.pl
    cG
    cM
    @24
    seqp1
    oveq12d
    syl
    3eqtr4rd
    eqeq12d
    syl5ibr
    expcom
    a2d
    fzind2
    mpcom
end
