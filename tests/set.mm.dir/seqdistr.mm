include "cseq.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "cfz.mm"
include "eqtr4d.mm"
include "seqhomo.mm"
include "seqcl.mm"
include "eqtr3d.mm"

theorem seqdistr
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let c.pl: class .+
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vz: setvar z
  assume seqdistr.1: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x .+ y ) e. S )
  assume seqdistr.2: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( C T ( x .+ y ) ) = ( ( C T x ) .+ ( C T y ) ) )
  assume seqdistr.3: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume seqdistr.4: |- ( ( ph /\ x e. ( M ... N ) ) -> ( G ` x ) e. S )
  assume seqdistr.5: |- ( ( ph /\ x e. ( M ... N ) ) -> ( F ` x ) = ( C T ( G ` x ) ) )

  disjoint x y
  disjoint C x
  disjoint C y
  disjoint G x
  disjoint G y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint .+ x
  disjoint .+ y
  disjoint F x
  disjoint ph x
  disjoint ph y
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint T y
  disjoint x z
  disjoint y z
  disjoint C z
  disjoint G z
  disjoint M z
  disjoint N z
  disjoint .+ z
  disjoint S z
  disjoint T z
  assert |- ( ph -> ( seq M ( .+ , F ) ` N ) = ( C T ( seq M ( .+ , G ) ` N ) ) )

  proof
    wph
    cN
    c.pl
    cG
    cM
    cseq
    cfv
    #
    vz
    cS
    cC
    vz
    cv
    #
    cT
    co
    #
    cmpt
    #
    cfv
    #
    cN
    c.pl
    cF
    cM
    cseq
    cfv
    cC
    @0
    cT
    co
    #
    wph
    vx
    vy
    c.pl
    c.pl
    cS
    cG
    cF
    @3
    cM
    cN
    seqdistr.1
    seqdistr.4
    seqdistr.3
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
    wa
    wa
    #
    cC
    @6
    @8
    c.pl
    co
    #
    cT
    co
    #
    cC
    @6
    cT
    co
    #
    cC
    @8
    cT
    co
    #
    c.pl
    co
    @11
    @3
    cfv
    #
    @6
    @3
    cfv
    #
    @8
    @3
    cfv
    #
    c.pl
    co
    seqdistr.2
    @10
    @11
    cS
    wcel
    @15
    @12
    wceq
    seqdistr.1
    vz
    @11
    @2
    @12
    cS
    @3
    @1
    @11
    cC
    cT
    oveq2
    @3
    eqid
    #
    cC
    @11
    cT
    ovex
    fvmpt
    syl
    @10
    @16
    @13
    @17
    @14
    c.pl
    @7
    @16
    @13
    wceq
    wph
    @9
    vz
    @6
    @2
    @13
    cS
    @3
    @1
    @6
    cC
    cT
    oveq2
    @18
    cC
    @6
    cT
    ovex
    fvmpt
    ad2antrl
    @9
    @17
    @14
    wceq
    wph
    @7
    vz
    @8
    @2
    @14
    cS
    @3
    @1
    @8
    cC
    cT
    oveq2
    @18
    cC
    @8
    cT
    ovex
    fvmpt
    ad2antll
    oveq12d
    3eqtr4d
    wph
    @6
    cM
    cN
    cfz
    co
    wcel
    wa
    #
    @6
    cG
    cfv
    #
    @3
    cfv
    #
    cC
    @20
    cT
    co
    #
    @6
    cF
    cfv
    @19
    @20
    cS
    wcel
    @21
    @22
    wceq
    seqdistr.4
    vz
    @20
    @2
    @22
    cS
    @3
    @1
    @20
    cC
    cT
    oveq2
    @18
    cC
    @20
    cT
    ovex
    fvmpt
    syl
    seqdistr.5
    eqtr4d
    seqhomo
    wph
    @0
    cS
    wcel
    @4
    @5
    wceq
    wph
    vx
    vy
    c.pl
    cS
    cG
    cM
    cN
    seqdistr.3
    seqdistr.4
    seqdistr.1
    seqcl
    vz
    @0
    @2
    @5
    cS
    @3
    @1
    @0
    cC
    cT
    oveq2
    @18
    cC
    @0
    cT
    ovex
    fvmpt
    syl
    eqtr3d
end
