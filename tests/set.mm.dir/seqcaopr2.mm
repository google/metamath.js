include "cv.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cseq.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "wral.mm"
include "cuz.mm"
include "elfzouz.mm"
include "adantl.mm"
include "cfz.mm"
include "wss.mm"
include "elfzouz2.mm"
include "fzss2.mm"
include "syl.mm"
include "sselda.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "syldan.mm"
include "adantlr.mm"
include "seqcl.mm"
include "fzofzp1.mm"
include "syl2an.mm"
include "anassrs.mm"
include "ralrimivva.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "2ralbidv.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "seqcaopr3.mm"

theorem seqcaopr2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let c.pl: class .+
  let cQ: class Q
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let vn: setvar n
  assume seqcaopr2.1: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x .+ y ) e. S )
  assume seqcaopr2.2: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x Q y ) e. S )
  assume seqcaopr2.3: |- ( ( ph /\ ( ( x e. S /\ y e. S ) /\ ( z e. S /\ w e. S ) ) ) -> ( ( x Q z ) .+ ( y Q w ) ) = ( ( x .+ y ) Q ( z .+ w ) ) )
  assume seqcaopr2.4: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume seqcaopr2.5: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) e. S )
  assume seqcaopr2.6: |- ( ( ph /\ k e. ( M ... N ) ) -> ( G ` k ) e. S )
  assume seqcaopr2.7: |- ( ( ph /\ k e. ( M ... N ) ) -> ( H ` k ) = ( ( F ` k ) Q ( G ` k ) ) )

  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint H k
  disjoint H z
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint k ph
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint G k
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint M k
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint Q k
  disjoint Q w
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint .+ w
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint S k
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint k n
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint H n
  disjoint N n
  disjoint n ph
  disjoint G n
  disjoint M n
  disjoint Q n
  disjoint .+ n
  assert |- ( ph -> ( seq M ( .+ , H ) ` N ) = ( ( seq M ( .+ , F ) ` N ) Q ( seq M ( .+ , G ) ` N ) ) )

  proof
    wph
    vx
    vy
    c.pl
    cQ
    cS
    vk
    vn
    cF
    cG
    cH
    cM
    cN
    seqcaopr2.1
    seqcaopr2.2
    seqcaopr2.4
    seqcaopr2.5
    seqcaopr2.6
    seqcaopr2.7
    wph
    vn
    cv
    #
    cM
    cN
    cfzo
    co
    wcel
    #
    wa
    #
    @0
    c.pl
    cG
    cM
    cseq
    cfv
    #
    cS
    wcel
    @0
    c1
    caddc
    co
    #
    cG
    cfv
    #
    cS
    wcel
    #
    @0
    c.pl
    cF
    cM
    cseq
    cfv
    #
    vz
    cv
    #
    cQ
    co
    #
    @4
    cF
    cfv
    #
    vw
    cv
    #
    cQ
    co
    #
    c.pl
    co
    #
    @7
    @10
    c.pl
    co
    #
    @8
    @11
    c.pl
    co
    #
    cQ
    co
    #
    wceq
    #
    vw
    cS
    wral
    vz
    cS
    wral
    #
    @7
    @3
    cQ
    co
    #
    @10
    @5
    cQ
    co
    #
    c.pl
    co
    #
    @14
    @3
    @5
    c.pl
    co
    #
    cQ
    co
    #
    wceq
    #
    @2
    vx
    vy
    c.pl
    cS
    cG
    cM
    @0
    @1
    @0
    cM
    cuz
    cfv
    wcel
    wph
    @0
    cM
    cN
    elfzouz
    adantl
    #
    @2
    vx
    cv
    #
    cM
    @0
    cfz
    co
    #
    wcel
    #
    @26
    cM
    cN
    cfz
    co
    #
    wcel
    #
    @26
    cG
    cfv
    #
    cS
    wcel
    #
    @2
    @27
    @29
    @26
    @2
    cN
    @0
    cuz
    cfv
    wcel
    #
    @27
    @29
    wss
    @1
    @33
    wph
    @0
    cM
    cN
    elfzouz2
    adantl
    @0
    cM
    cN
    fzss2
    syl
    sselda
    #
    @2
    vk
    cv
    #
    cG
    cfv
    #
    cS
    wcel
    #
    vk
    @29
    wral
    #
    @30
    @32
    wph
    @38
    @1
    wph
    @37
    vk
    @29
    seqcaopr2.6
    ralrimiva
    #
    adantr
    @37
    @32
    vk
    @26
    @29
    @35
    @26
    wceq
    #
    @36
    @31
    cS
    @35
    @26
    cG
    fveq2
    eleq1d
    rspccva
    sylan
    syldan
    wph
    @26
    cS
    wcel
    vy
    cv
    #
    cS
    wcel
    wa
    #
    @26
    @41
    c.pl
    co
    #
    cS
    wcel
    @1
    seqcaopr2.1
    adantlr
    #
    seqcl
    wph
    @38
    @4
    @29
    wcel
    #
    @6
    @1
    @39
    cM
    cN
    @0
    fzofzp1
    #
    @37
    @6
    vk
    @4
    @29
    @35
    @4
    wceq
    #
    @36
    @5
    cS
    @35
    @4
    cG
    fveq2
    eleq1d
    rspccva
    syl2an
    @2
    @7
    cS
    wcel
    @10
    cS
    wcel
    #
    @26
    @8
    cQ
    co
    #
    @41
    @11
    cQ
    co
    #
    c.pl
    co
    #
    @43
    @15
    cQ
    co
    #
    wceq
    #
    vw
    cS
    wral
    vz
    cS
    wral
    #
    vy
    cS
    wral
    vx
    cS
    wral
    #
    @18
    @2
    vx
    vy
    c.pl
    cS
    cF
    cM
    @0
    @25
    @2
    @28
    @30
    @26
    cF
    cfv
    #
    cS
    wcel
    #
    @34
    wph
    @30
    @57
    @1
    wph
    @35
    cF
    cfv
    #
    cS
    wcel
    #
    vk
    @29
    wral
    #
    @30
    @57
    wph
    @59
    vk
    @29
    seqcaopr2.5
    ralrimiva
    #
    @59
    @57
    vk
    @26
    @29
    @40
    @58
    @56
    cS
    @35
    @26
    cF
    fveq2
    eleq1d
    rspccva
    sylan
    adantlr
    syldan
    @44
    seqcl
    wph
    @60
    @45
    @48
    @1
    @61
    @46
    @59
    @48
    vk
    @4
    @29
    @47
    @58
    @10
    cS
    @35
    @4
    cF
    fveq2
    eleq1d
    rspccva
    syl2an
    wph
    @55
    @1
    wph
    @54
    vx
    vy
    cS
    cS
    wph
    @42
    wa
    @53
    vz
    vw
    cS
    cS
    wph
    @42
    @8
    cS
    wcel
    @11
    cS
    wcel
    wa
    @53
    seqcaopr2.3
    anassrs
    ralrimivva
    ralrimivva
    adantr
    @54
    @18
    @9
    @50
    c.pl
    co
    #
    @7
    @41
    c.pl
    co
    #
    @15
    cQ
    co
    #
    wceq
    #
    vw
    cS
    wral
    vz
    cS
    wral
    vx
    vy
    @7
    @10
    cS
    cS
    @26
    @7
    wceq
    #
    @53
    @65
    vz
    vw
    cS
    cS
    @66
    @51
    @62
    @52
    @64
    @66
    @49
    @9
    @50
    c.pl
    @26
    @7
    @8
    cQ
    oveq1
    oveq1d
    @66
    @43
    @63
    @15
    cQ
    @26
    @7
    @41
    c.pl
    oveq1
    oveq1d
    eqeq12d
    2ralbidv
    @41
    @10
    wceq
    #
    @65
    @17
    vz
    vw
    cS
    cS
    @67
    @62
    @13
    @64
    @16
    @67
    @50
    @12
    @9
    c.pl
    @41
    @10
    @11
    cQ
    oveq1
    oveq2d
    @67
    @63
    @14
    @15
    cQ
    @41
    @10
    @7
    c.pl
    oveq2
    oveq1d
    eqeq12d
    2ralbidv
    rspc2va
    syl21anc
    @17
    @24
    @19
    @12
    c.pl
    co
    #
    @14
    @3
    @11
    c.pl
    co
    #
    cQ
    co
    #
    wceq
    vz
    vw
    @3
    @5
    cS
    cS
    @8
    @3
    wceq
    #
    @13
    @68
    @16
    @70
    @71
    @9
    @19
    @12
    c.pl
    @8
    @3
    @7
    cQ
    oveq2
    oveq1d
    @71
    @15
    @69
    @14
    cQ
    @8
    @3
    @11
    c.pl
    oveq1
    oveq2d
    eqeq12d
    @11
    @5
    wceq
    #
    @68
    @21
    @70
    @23
    @72
    @12
    @20
    @19
    c.pl
    @11
    @5
    @10
    cQ
    oveq2
    oveq2d
    @72
    @69
    @22
    @14
    cQ
    @11
    @5
    @3
    c.pl
    oveq2
    oveq2d
    eqeq12d
    rspc2va
    syl21anc
    seqcaopr3
end
