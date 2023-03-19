include "cdv.mm"
include "co.mm"
include "cdm.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "cnt.mm"
include "eqid.mm"
include "dvbssntr.mm"
include "ctop.mm"
include "wcel.mm"
include "cuni.mm"
include "wss.mm"
include "cvv.mm"
include "cnfldtop.mm"
include "cc.mm"
include "cnex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "resttop.mm"
include "sylancr.mm"
include "ctopon.mm"
include "wceq.mm"
include "cnfldtopon.mm"
include "resttopon.mm"
include "toponuni.mm"
include "syl.mm"
include "sseqtrd.mm"
include "ntrss2.mm"
include "syl2anc.mm"
include "sstrd.mm"

theorem dvbss
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cF: class F
  let vx: setvar x
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cK: class K
  let cJ: class J
  assume dvcl.s: |- ( ph -> S C_ CC )
  assume dvcl.f: |- ( ph -> F : A --> CC )
  assume dvcl.a: |- ( ph -> A C_ S )


  assert |- ( ph -> dom ( S _D F ) C_ A )

  proof
    wph
    cS
    cF
    cdv
    co
    cdm
    cA
    ccnfld
    ctopn
    cfv
    #
    cS
    crest
    co
    #
    cnt
    cfv
    cfv
    #
    cA
    wph
    cA
    cS
    cF
    @1
    @0
    dvcl.s
    dvcl.f
    dvcl.a
    @1
    eqid
    @0
    eqid
    #
    dvbssntr
    wph
    @1
    ctop
    wcel
    #
    cA
    @1
    cuni
    #
    wss
    @2
    cA
    wss
    wph
    @0
    ctop
    wcel
    cS
    cvv
    wcel
    #
    @4
    @0
    @3
    cnfldtop
    wph
    cS
    cc
    wss
    #
    cc
    cvv
    wcel
    @6
    dvcl.s
    cnex
    cS
    cc
    cvv
    ssexg
    sylancl
    cS
    @0
    cvv
    resttop
    sylancr
    wph
    cA
    cS
    @5
    dvcl.a
    wph
    @1
    cS
    ctopon
    cfv
    wcel
    #
    cS
    @5
    wceq
    wph
    @0
    cc
    ctopon
    cfv
    wcel
    @7
    @8
    @0
    @3
    cnfldtopon
    dvcl.s
    cS
    @0
    cc
    resttopon
    sylancr
    cS
    @1
    toponuni
    syl
    sseqtrd
    cA
    @1
    @5
    @5
    eqid
    ntrss2
    syl2anc
    sstrd
end
