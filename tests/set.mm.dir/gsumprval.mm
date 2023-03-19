include "cgsu.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cseq.mm"
include "cfv.mm"
include "cuz.mm"
include "wcel.mm"
include "cz.mm"
include "uzid.mm"
include "syl.mm"
include "peano2uz.mm"
include "cfz.mm"
include "wf.mm"
include "cpr.mm"
include "wceq.mm"
include "fzpr.mm"
include "eqcomd.mm"
include "preq2d.mm"
include "eqtrd.mm"
include "feq2d.mm"
include "mpbird.mm"
include "gsumval2.mm"
include "seqp1.mm"
include "seq1.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "3eqtrd.mm"

theorem gsumprval
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let cV: class V
  assume gsumprval.b: |- B = ( Base ` G )
  assume gsumprval.p: |- .+ = ( +g ` G )
  assume gsumprval.g: |- ( ph -> G e. V )
  assume gsumprval.m: |- ( ph -> M e. ZZ )
  assume gsumprval.n: |- ( ph -> N = ( M + 1 ) )
  assume gsumprval.f: |- ( ph -> F : { M , N } --> B )


  assert |- ( ph -> ( G gsum F ) = ( ( F ` M ) .+ ( F ` N ) ) )

  proof
    wph
    cG
    cF
    cgsu
    co
    cM
    c1
    caddc
    co
    #
    c.pl
    cF
    cM
    cseq
    #
    cfv
    #
    cM
    @1
    cfv
    #
    @0
    cF
    cfv
    #
    c.pl
    co
    #
    cM
    cF
    cfv
    #
    cN
    cF
    cfv
    #
    c.pl
    co
    wph
    cB
    c.pl
    cF
    cG
    cM
    @0
    cV
    gsumprval.b
    gsumprval.p
    gsumprval.g
    wph
    cM
    cM
    cuz
    cfv
    #
    wcel
    #
    @0
    @8
    wcel
    wph
    cM
    cz
    wcel
    #
    @9
    gsumprval.m
    cM
    uzid
    syl
    #
    cM
    cM
    peano2uz
    syl
    wph
    cM
    @0
    cfz
    co
    #
    cB
    cF
    wf
    cM
    cN
    cpr
    #
    cB
    cF
    wf
    gsumprval.f
    wph
    @12
    @13
    cB
    cF
    wph
    @12
    cM
    @0
    cpr
    #
    @13
    wph
    @10
    @12
    @14
    wceq
    gsumprval.m
    cM
    fzpr
    syl
    wph
    @0
    cN
    cM
    wph
    cN
    @0
    gsumprval.n
    eqcomd
    #
    preq2d
    eqtrd
    feq2d
    mpbird
    gsumval2
    wph
    @9
    @2
    @5
    wceq
    @11
    c.pl
    cF
    cM
    cM
    seqp1
    syl
    wph
    @3
    @6
    @4
    @7
    c.pl
    wph
    @10
    @3
    @6
    wceq
    gsumprval.m
    c.pl
    cF
    cM
    seq1
    syl
    wph
    @0
    cN
    cF
    @15
    fveq2d
    oveq12d
    3eqtrd
end
