include "cseq.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cz.mm"
include "wcel.mm"
include "cuz.mm"
include "uzid.mm"
include "syl.mm"
include "seqsplit.mm"
include "wceq.mm"
include "seq1.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem seq1p
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.pl: class .+
  let cS: class S
  let cF: class F
  let cM: class M
  let cN: class N
  let vn: setvar n
  let cK: class K
  assume seqsplit.1: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x .+ y ) e. S )
  assume seqsplit.2: |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) )
  assume seqsplit.3: |- ( ph -> N e. ( ZZ>= ` ( M + 1 ) ) )
  assume seq1p.4: |- ( ph -> M e. ZZ )
  assume seq1p.5: |- ( ( ph /\ x e. ( M ... N ) ) -> ( F ` x ) e. S )

  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint M n
  disjoint n ph
  disjoint N n
  disjoint .+ n
  assert |- ( ph -> ( seq M ( .+ , F ) ` N ) = ( ( F ` M ) .+ ( seq ( M + 1 ) ( .+ , F ) ` N ) ) )

  proof
    wph
    cN
    c.pl
    cF
    cM
    cseq
    #
    cfv
    cM
    @0
    cfv
    #
    cN
    c.pl
    cF
    cM
    c1
    caddc
    co
    cseq
    cfv
    #
    c.pl
    co
    cM
    cF
    cfv
    #
    @2
    c.pl
    co
    wph
    vx
    vy
    vz
    c.pl
    cS
    cF
    cM
    cM
    cN
    seqsplit.1
    seqsplit.2
    seqsplit.3
    wph
    cM
    cz
    wcel
    #
    cM
    cM
    cuz
    cfv
    wcel
    seq1p.4
    cM
    uzid
    syl
    seq1p.5
    seqsplit
    wph
    @1
    @3
    @2
    c.pl
    wph
    @4
    @1
    @3
    wceq
    seq1p.4
    c.pl
    cF
    cM
    seq1
    syl
    oveq1d
    eqtrd
end
