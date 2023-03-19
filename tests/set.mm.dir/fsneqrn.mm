include "wceq.mm"
include "cfv.mm"
include "crn.mm"
include "wcel.mm"
include "wa.mm"
include "wfn.mm"
include "wf.mm"
include "dffn3.mm"
include "sylib.mm"
include "csn.mm"
include "snidg.mm"
include "syl.mm"
include "a1i.mm"
include "eqcomd.mm"
include "eleqtrd.mm"
include "ffvelrnd.mm"
include "adantr.mm"
include "simpr.mm"
include "rneqd.mm"
include "ex.mm"
include "cvv.mm"
include "dffn2.mm"
include "feq2d.mm"
include "mpbid.mm"
include "rnsnf.mm"
include "elsni.mm"
include "fsneq.mm"
include "mpbird.mm"
include "impbid.mm"

theorem fsneqrn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  assume fsneqrn.a: |- ( ph -> A e. V )
  assume fsneqrn.b: |- B = { A }
  assume fsneqrn.f: |- ( ph -> F Fn B )
  assume fsneqrn.g: |- ( ph -> G Fn B )


  assert |- ( ph -> ( F = G <-> ( F ` A ) e. ran G ) )

  proof
    wph
    cF
    cG
    wceq
    #
    cA
    cF
    cfv
    #
    cG
    crn
    #
    wcel
    #
    wph
    @0
    @3
    wph
    @0
    wa
    #
    @1
    cF
    crn
    #
    @2
    wph
    @1
    @5
    wcel
    @0
    wph
    cB
    @5
    cA
    cF
    wph
    cF
    cB
    wfn
    #
    cB
    @5
    cF
    wf
    fsneqrn.f
    cB
    cF
    dffn3
    sylib
    wph
    cA
    cA
    csn
    #
    cB
    wph
    cA
    cV
    wcel
    #
    cA
    @7
    wcel
    fsneqrn.a
    cA
    cV
    snidg
    syl
    wph
    cB
    @7
    cB
    @7
    wceq
    wph
    fsneqrn.b
    a1i
    #
    eqcomd
    eleqtrd
    ffvelrnd
    adantr
    @4
    cF
    cG
    wph
    @0
    simpr
    rneqd
    eleqtrd
    ex
    wph
    @3
    @0
    wph
    @3
    wa
    #
    @0
    @1
    cA
    cG
    cfv
    #
    wceq
    #
    @10
    @1
    @11
    csn
    #
    wcel
    @12
    @10
    @1
    @2
    @13
    wph
    @3
    simpr
    wph
    @2
    @13
    wceq
    @3
    wph
    cA
    cvv
    cG
    cV
    fsneqrn.a
    wph
    cB
    cvv
    cG
    wf
    #
    @7
    cvv
    cG
    wf
    wph
    cG
    cB
    wfn
    #
    @14
    fsneqrn.g
    cB
    cG
    dffn2
    sylib
    wph
    cB
    @7
    cvv
    cG
    @9
    feq2d
    mpbid
    rnsnf
    adantr
    eleqtrd
    @1
    @11
    elsni
    syl
    @10
    cA
    cB
    cF
    cG
    cV
    wph
    @8
    @3
    fsneqrn.a
    adantr
    fsneqrn.b
    wph
    @6
    @3
    fsneqrn.f
    adantr
    wph
    @15
    @3
    fsneqrn.g
    adantr
    fsneq
    mpbird
    ex
    impbid
end
