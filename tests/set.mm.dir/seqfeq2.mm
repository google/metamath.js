include "cuz.mm"
include "cfv.mm"
include "cseq.mm"
include "cres.mm"
include "wfn.mm"
include "wss.mm"
include "wcel.mm"
include "cz.mm"
include "eluzel2.mm"
include "seqfn.mm"
include "3syl.mm"
include "uzss.mm"
include "syl.mm"
include "fnssres.mm"
include "syl2anc.mm"
include "eluzelz.mm"
include "cv.mm"
include "wa.mm"
include "wceq.mm"
include "fvres.mm"
include "adantl.mm"
include "adantr.mm"
include "simpr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "elfzuz.mm"
include "sylan2.mm"
include "adantlr.mm"
include "seqfveq2.mm"
include "eqtrd.mm"
include "eqfnfvd.mm"

theorem seqfeq2
  let wph: wff ph
  let c.pl: class .+
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cK: class K
  let cM: class M
  let vn: setvar n
  let vx: setvar x
  let cN: class N
  assume seqfveq2.1: |- ( ph -> K e. ( ZZ>= ` M ) )
  assume seqfveq2.2: |- ( ph -> ( seq M ( .+ , F ) ` K ) = ( G ` K ) )
  assume seqfeq2.4: |- ( ( ph /\ k e. ( ZZ>= ` ( K + 1 ) ) ) -> ( F ` k ) = ( G ` k ) )

  disjoint F k
  disjoint G k
  disjoint K k
  disjoint k ph
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint F n
  disjoint F x
  disjoint G n
  disjoint G x
  disjoint K n
  disjoint K x
  disjoint N k
  disjoint N n
  disjoint N x
  disjoint n ph
  disjoint ph x
  disjoint M n
  disjoint M x
  disjoint .+ n
  disjoint .+ x
  assert |- ( ph -> ( seq M ( .+ , F ) |` ( ZZ>= ` K ) ) = seq K ( .+ , G ) )

  proof
    wph
    vx
    cK
    cuz
    cfv
    #
    c.pl
    cF
    cM
    cseq
    #
    @0
    cres
    #
    c.pl
    cG
    cK
    cseq
    #
    wph
    @1
    cM
    cuz
    cfv
    #
    wfn
    #
    @0
    @4
    wss
    #
    @2
    @0
    wfn
    wph
    cK
    @4
    wcel
    #
    cM
    cz
    wcel
    @5
    seqfveq2.1
    cM
    cK
    eluzel2
    c.pl
    cF
    cM
    seqfn
    3syl
    wph
    @7
    @6
    seqfveq2.1
    cM
    cK
    uzss
    syl
    @4
    @0
    @1
    fnssres
    syl2anc
    wph
    @7
    cK
    cz
    wcel
    @3
    @0
    wfn
    seqfveq2.1
    cM
    cK
    eluzelz
    c.pl
    cG
    cK
    seqfn
    3syl
    wph
    vx
    cv
    #
    @0
    wcel
    #
    wa
    #
    @8
    @2
    cfv
    #
    @8
    @1
    cfv
    #
    @8
    @3
    cfv
    @9
    @11
    @12
    wceq
    wph
    @8
    @0
    @1
    fvres
    adantl
    @10
    c.pl
    vk
    cF
    cG
    cK
    cM
    @8
    wph
    @7
    @9
    seqfveq2.1
    adantr
    wph
    cK
    @1
    cfv
    cK
    cG
    cfv
    wceq
    @9
    seqfveq2.2
    adantr
    wph
    @9
    simpr
    wph
    vk
    cv
    #
    cK
    c1
    caddc
    co
    #
    @8
    cfz
    co
    wcel
    #
    @13
    cF
    cfv
    @13
    cG
    cfv
    wceq
    #
    @9
    @15
    wph
    @13
    @14
    cuz
    cfv
    wcel
    @16
    @13
    @14
    @8
    elfzuz
    seqfeq2.4
    sylan2
    adantlr
    seqfveq2
    eqtrd
    eqfnfvd
end
