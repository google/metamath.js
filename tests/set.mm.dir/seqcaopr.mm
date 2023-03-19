include "cv.mm"
include "caovclg.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "simpl.mm"
include "simprrl.mm"
include "simprlr.mm"
include "caovcomg.mm"
include "syl12anc.mm"
include "oveq1d.mm"
include "simprrr.mm"
include "caovassg.mm"
include "syl13anc.mm"
include "3eqtr3d.mm"
include "oveq2d.mm"
include "simprll.mm"
include "adantrl.mm"
include "3eqtr4d.mm"
include "seqcaopr2.mm"

theorem seqcaopr
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.pl: class .+
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume seqcaopr.1: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x .+ y ) e. S )
  assume seqcaopr.2: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x .+ y ) = ( y .+ x ) )
  assume seqcaopr.3: |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) )
  assume seqcaopr.4: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume seqcaopr.5: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) e. S )
  assume seqcaopr.6: |- ( ( ph /\ k e. ( M ... N ) ) -> ( G ` k ) e. S )
  assume seqcaopr.7: |- ( ( ph /\ k e. ( M ... N ) ) -> ( H ` k ) = ( ( F ` k ) .+ ( G ` k ) ) )

  disjoint F k
  disjoint G k
  disjoint H k
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint k ph
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint M k
  disjoint .+ k
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint N k
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a k
  disjoint F a
  disjoint b c
  disjoint b d
  disjoint b k
  disjoint F b
  disjoint c d
  disjoint c k
  disjoint F c
  disjoint d k
  disjoint F d
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G d
  disjoint H c
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint a ph
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint b ph
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint c ph
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint d ph
  disjoint M a
  disjoint M b
  disjoint M c
  disjoint M d
  disjoint .+ a
  disjoint .+ b
  disjoint .+ c
  disjoint .+ d
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint N a
  disjoint N b
  disjoint N c
  assert |- ( ph -> ( seq M ( .+ , H ) ` N ) = ( ( seq M ( .+ , F ) ` N ) .+ ( seq M ( .+ , G ) ` N ) ) )

  proof
    wph
    va
    vb
    vc
    vd
    c.pl
    c.pl
    cS
    vk
    cF
    cG
    cH
    cM
    cN
    wph
    vx
    vy
    va
    cv
    #
    vb
    cv
    #
    cS
    cS
    cS
    c.pl
    seqcaopr.1
    caovclg
    #
    @2
    wph
    @0
    cS
    wcel
    #
    @1
    cS
    wcel
    #
    wa
    #
    vc
    cv
    #
    cS
    wcel
    #
    vd
    cv
    #
    cS
    wcel
    #
    wa
    #
    wa
    #
    wa
    #
    @0
    @6
    @1
    @8
    c.pl
    co
    #
    c.pl
    co
    #
    c.pl
    co
    #
    @0
    @1
    @6
    @8
    c.pl
    co
    #
    c.pl
    co
    #
    c.pl
    co
    #
    @0
    @6
    c.pl
    co
    @13
    c.pl
    co
    #
    @0
    @1
    c.pl
    co
    @16
    c.pl
    co
    #
    @12
    @14
    @17
    @0
    c.pl
    @12
    @6
    @1
    c.pl
    co
    #
    @8
    c.pl
    co
    #
    @1
    @6
    c.pl
    co
    #
    @8
    c.pl
    co
    #
    @14
    @17
    @12
    @21
    @23
    @8
    c.pl
    @12
    wph
    @7
    @4
    @21
    @23
    wceq
    wph
    @11
    simpl
    #
    wph
    @5
    @7
    @9
    simprrl
    #
    wph
    @3
    @4
    @10
    simprlr
    #
    wph
    vx
    vy
    @6
    @1
    cS
    c.pl
    seqcaopr.2
    caovcomg
    syl12anc
    oveq1d
    @12
    wph
    @7
    @4
    @9
    @22
    @14
    wceq
    @25
    @26
    @27
    wph
    @5
    @7
    @9
    simprrr
    #
    wph
    vx
    vy
    vz
    @6
    @1
    @8
    cS
    c.pl
    seqcaopr.3
    caovassg
    syl13anc
    @12
    wph
    @4
    @7
    @9
    @24
    @17
    wceq
    @25
    @27
    @26
    @28
    wph
    vx
    vy
    vz
    @1
    @6
    @8
    cS
    c.pl
    seqcaopr.3
    caovassg
    syl13anc
    3eqtr3d
    oveq2d
    @12
    wph
    @3
    @7
    @13
    cS
    wcel
    #
    @19
    @15
    wceq
    @25
    wph
    @3
    @4
    @10
    simprll
    #
    @26
    @12
    wph
    @4
    @9
    @29
    @25
    @27
    @28
    wph
    vx
    vy
    @1
    @8
    cS
    cS
    cS
    c.pl
    seqcaopr.1
    caovclg
    syl12anc
    wph
    vx
    vy
    vz
    @0
    @6
    @13
    cS
    c.pl
    seqcaopr.3
    caovassg
    syl13anc
    @12
    wph
    @3
    @4
    @16
    cS
    wcel
    #
    @20
    @18
    wceq
    @25
    @30
    @27
    wph
    @10
    @31
    @5
    wph
    vx
    vy
    @6
    @8
    cS
    cS
    cS
    c.pl
    seqcaopr.1
    caovclg
    adantrl
    wph
    vx
    vy
    vz
    @0
    @1
    @16
    cS
    c.pl
    seqcaopr.3
    caovassg
    syl13anc
    3eqtr4d
    seqcaopr.4
    seqcaopr.5
    seqcaopr.6
    seqcaopr.7
    seqcaopr2
end
