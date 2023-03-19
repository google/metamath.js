include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "cseq.mm"
include "wceq.mm"
include "cuz.mm"
include "eluzfz2.mm"
include "syl.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "ffvelrnd.mm"
include "cz.mm"
include "eluzel2.mm"
include "seq1.mm"
include "3syl.mm"
include "eluzfz1.mm"
include "sseldd.mm"
include "eqeltrd.mm"
include "caovcomd.mm"
include "a1i.mm"
include "cfzo.mm"
include "wa.mm"
include "oveq1.mm"
include "elfzouz.mm"
include "adantl.mm"
include "seqp1.mm"
include "w3a.mm"
include "adantlr.mm"
include "adantr.mm"
include "wss.mm"
include "wf.mm"
include "elfzouz2.mm"
include "fzss2.mm"
include "sstrd.mm"
include "sselda.mm"
include "seqcl.mm"
include "fzofzp1.mm"
include "caovassd.mm"
include "eqtr4d.mm"
include "3eqtr4d.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "a2d.mm"
include "fzind2.mm"
include "mpcom.mm"

theorem seqf1olem2a
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cC: class C
  let c.pl: class .+
  let cS: class S
  let cG: class G
  let cK: class K
  let cM: class M
  let cN: class N
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let cF: class F
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let cJ: class J
  let cH: class H
  assume seqf1o.1: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x .+ y ) e. S )
  assume seqf1o.2: |- ( ( ph /\ ( x e. C /\ y e. C ) ) -> ( x .+ y ) = ( y .+ x ) )
  assume seqf1o.3: |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) )
  assume seqf1o.4: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume seqf1o.5: |- ( ph -> C C_ S )
  assume seqf1olem2a.1: |- ( ph -> G : A --> C )
  assume seqf1olem2a.3: |- ( ph -> K e. A )
  assume seqf1olem2a.4: |- ( ph -> ( M ... N ) C_ A )

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint f g
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint g k
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint f m
  disjoint f n
  disjoint G f
  disjoint g m
  disjoint g n
  disjoint G g
  disjoint k m
  disjoint k n
  disjoint G k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint G m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint G n
  disjoint f s
  disjoint f t
  disjoint f w
  disjoint M f
  disjoint g s
  disjoint g t
  disjoint g w
  disjoint M g
  disjoint k s
  disjoint k t
  disjoint k w
  disjoint M k
  disjoint m s
  disjoint m t
  disjoint m w
  disjoint M m
  disjoint n s
  disjoint n t
  disjoint n w
  disjoint M n
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint M s
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint M t
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint M w
  disjoint .+ f
  disjoint .+ g
  disjoint .+ k
  disjoint .+ m
  disjoint .+ n
  disjoint .+ s
  disjoint .+ t
  disjoint .+ w
  disjoint J f
  disjoint J g
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint N f
  disjoint N g
  disjoint N k
  disjoint N m
  disjoint N n
  disjoint K k
  disjoint K m
  disjoint K n
  disjoint f ph
  disjoint g ph
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph s
  disjoint ph t
  disjoint ph w
  disjoint S k
  disjoint S s
  disjoint S t
  disjoint S w
  disjoint C f
  disjoint C g
  disjoint C k
  disjoint C s
  disjoint C t
  disjoint C w
  disjoint H k
  assert |- ( ph -> ( ( G ` K ) .+ ( seq M ( .+ , G ) ` N ) ) = ( ( seq M ( .+ , G ) ` N ) .+ ( G ` K ) ) )

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
    cK
    cG
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
    c.pl
    co
    #
    @4
    @2
    c.pl
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
    seqf1o.4
    cM
    cN
    eluzfz2
    syl
    wph
    @2
    vm
    cv
    #
    @3
    cfv
    #
    c.pl
    co
    #
    @11
    @2
    c.pl
    co
    #
    wceq
    #
    wi
    wph
    @2
    cM
    @3
    cfv
    #
    c.pl
    co
    #
    @15
    @2
    c.pl
    co
    #
    wceq
    #
    wi
    #
    wph
    @2
    vn
    cv
    #
    @3
    cfv
    #
    c.pl
    co
    #
    @21
    @2
    c.pl
    co
    #
    wceq
    #
    wi
    wph
    @2
    @20
    c1
    caddc
    co
    #
    @3
    cfv
    #
    c.pl
    co
    #
    @26
    @2
    c.pl
    co
    #
    wceq
    #
    wi
    wph
    @7
    wi
    vm
    vn
    cN
    cM
    cN
    @10
    cM
    wceq
    #
    @14
    @18
    wph
    @30
    @12
    @16
    @13
    @17
    @30
    @11
    @15
    @2
    c.pl
    @10
    cM
    @3
    fveq2
    #
    oveq2d
    @30
    @11
    @15
    @2
    c.pl
    @31
    oveq1d
    eqeq12d
    imbi2d
    @10
    @20
    wceq
    #
    @14
    @24
    wph
    @32
    @12
    @22
    @13
    @23
    @32
    @11
    @21
    @2
    c.pl
    @10
    @20
    @3
    fveq2
    #
    oveq2d
    @32
    @11
    @21
    @2
    c.pl
    @33
    oveq1d
    eqeq12d
    imbi2d
    @10
    @25
    wceq
    #
    @14
    @29
    wph
    @34
    @12
    @27
    @13
    @28
    @34
    @11
    @26
    @2
    c.pl
    @10
    @25
    @3
    fveq2
    #
    oveq2d
    @34
    @11
    @26
    @2
    c.pl
    @35
    oveq1d
    eqeq12d
    imbi2d
    @10
    cN
    wceq
    #
    @14
    @7
    wph
    @36
    @12
    @5
    @13
    @6
    @36
    @11
    @4
    @2
    c.pl
    @10
    cN
    @3
    fveq2
    #
    oveq2d
    @36
    @11
    @4
    @2
    c.pl
    @37
    oveq1d
    eqeq12d
    imbi2d
    @19
    @9
    wph
    vx
    vy
    @2
    @15
    cC
    c.pl
    seqf1o.2
    wph
    cA
    cC
    cK
    cG
    seqf1olem2a.1
    seqf1olem2a.3
    ffvelrnd
    #
    wph
    @15
    cM
    cG
    cfv
    #
    cC
    wph
    @9
    cM
    cz
    wcel
    @15
    @39
    wceq
    seqf1o.4
    cM
    cN
    eluzel2
    c.pl
    cG
    cM
    seq1
    3syl
    wph
    cA
    cC
    cM
    cG
    seqf1olem2a.1
    wph
    @0
    cA
    cM
    seqf1olem2a.4
    wph
    @9
    cM
    @0
    wcel
    seqf1o.4
    cM
    cN
    eluzfz1
    syl
    sseldd
    ffvelrnd
    eqeltrd
    caovcomd
    a1i
    @20
    cM
    cN
    cfzo
    co
    wcel
    #
    wph
    @24
    @29
    wph
    @40
    @24
    @29
    wi
    @24
    @29
    wph
    @40
    wa
    #
    @22
    @25
    cG
    cfv
    #
    c.pl
    co
    #
    @23
    @42
    c.pl
    co
    #
    wceq
    @22
    @23
    @42
    c.pl
    oveq1
    @41
    @27
    @43
    @28
    @44
    @41
    @27
    @2
    @21
    @42
    c.pl
    co
    #
    c.pl
    co
    @43
    @41
    @26
    @45
    @2
    c.pl
    @41
    @20
    @8
    wcel
    #
    @26
    @45
    wceq
    @40
    @46
    wph
    @20
    cM
    cN
    elfzouz
    adantl
    #
    c.pl
    cG
    cM
    @20
    seqp1
    syl
    #
    oveq2d
    @41
    vx
    vy
    vz
    @2
    @21
    @42
    cS
    c.pl
    wph
    vx
    cv
    #
    cS
    wcel
    #
    vy
    cv
    #
    cS
    wcel
    #
    vz
    cv
    #
    cS
    wcel
    w3a
    @49
    @51
    c.pl
    co
    #
    @53
    c.pl
    co
    @49
    @51
    @53
    c.pl
    co
    c.pl
    co
    wceq
    @40
    seqf1o.3
    adantlr
    #
    wph
    @2
    cS
    wcel
    @40
    wph
    cC
    cS
    @2
    seqf1o.5
    @38
    sseldd
    adantr
    #
    @41
    vx
    vy
    c.pl
    cS
    cG
    cM
    @20
    @47
    @41
    @49
    cM
    @20
    cfz
    co
    #
    wcel
    #
    wa
    #
    cC
    cS
    @49
    cG
    cfv
    @41
    cC
    cS
    wss
    #
    @58
    wph
    @60
    @40
    seqf1o.5
    adantr
    #
    adantr
    @59
    cA
    cC
    @49
    cG
    @41
    cA
    cC
    cG
    wf
    #
    @58
    wph
    @62
    @40
    seqf1olem2a.1
    adantr
    #
    adantr
    @41
    @57
    cA
    @49
    @41
    @57
    @0
    cA
    @41
    cN
    @20
    cuz
    cfv
    wcel
    #
    @57
    @0
    wss
    @40
    @64
    wph
    @20
    cM
    cN
    elfzouz2
    adantl
    @20
    cM
    cN
    fzss2
    syl
    wph
    @0
    cA
    wss
    @40
    seqf1olem2a.4
    adantr
    #
    sstrd
    sselda
    ffvelrnd
    sseldd
    wph
    @50
    @52
    wa
    @54
    cS
    wcel
    @40
    seqf1o.1
    adantlr
    seqcl
    #
    @41
    cC
    cS
    @42
    @61
    @41
    cA
    cC
    @25
    cG
    @63
    @41
    @0
    cA
    @25
    @65
    @40
    @25
    @0
    wcel
    wph
    cM
    cN
    @20
    fzofzp1
    adantl
    sseldd
    ffvelrnd
    #
    sseldd
    #
    caovassd
    eqtr4d
    @41
    @45
    @2
    c.pl
    co
    @21
    @42
    @2
    c.pl
    co
    #
    c.pl
    co
    #
    @28
    @44
    @41
    vx
    vy
    vz
    @21
    @42
    @2
    cS
    c.pl
    @55
    @66
    @68
    @56
    caovassd
    @41
    @26
    @45
    @2
    c.pl
    @48
    oveq1d
    @41
    @44
    @21
    @2
    @42
    c.pl
    co
    #
    c.pl
    co
    @70
    @41
    vx
    vy
    vz
    @21
    @2
    @42
    cS
    c.pl
    @55
    @66
    @56
    @68
    caovassd
    @41
    @69
    @71
    @21
    c.pl
    @41
    vx
    vy
    @42
    @2
    cC
    c.pl
    wph
    @49
    cC
    wcel
    @51
    cC
    wcel
    wa
    @54
    @51
    @49
    c.pl
    co
    wceq
    @40
    seqf1o.2
    adantlr
    @67
    wph
    @2
    cC
    wcel
    @40
    @38
    adantr
    caovcomd
    oveq2d
    eqtr4d
    3eqtr4d
    eqeq12d
    syl5ibr
    expcom
    a2d
    fzind2
    mpcom
end
