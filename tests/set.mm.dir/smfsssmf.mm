include "cdm.mm"
include "nfv.mm"
include "cuni.mm"
include "eqid.mm"
include "smfdmss.mm"
include "unissd.mm"
include "sstrd.mm"
include "smff.mm"
include "cv.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "wss.mm"
include "csalg.mm"
include "ssrest.mm"
include "syl2anc.mm"
include "adantr.mm"
include "csmblfn.mm"
include "simpr.mm"
include "smfpreimalt.mm"
include "sseldd.mm"
include "issmfd.mm"

theorem smfsssmf
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cF: class F
  let va: setvar a
  let vx: setvar x
  let vk: setvar k
  assume smfsssmf.r: |- ( ph -> R e. SAlg )
  assume smfsssmf.s: |- ( ph -> S e. SAlg )
  assume smfsssmf.i: |- ( ph -> R C_ S )
  assume smfsssmf.f: |- ( ph -> F e. ( SMblFn ` R ) )


  assert |- ( ph -> F e. ( SMblFn ` S ) )

  proof
    wph
    vx
    cF
    cdm
    #
    cS
    cF
    va
    wph
    va
    nfv
    smfsssmf.s
    wph
    @0
    cR
    cuni
    cS
    cuni
    wph
    @0
    cR
    cF
    smfsssmf.r
    smfsssmf.f
    @0
    eqid
    #
    smfdmss
    wph
    cR
    cS
    smfsssmf.i
    unissd
    sstrd
    wph
    @0
    cR
    cF
    smfsssmf.r
    smfsssmf.f
    @1
    smff
    wph
    va
    cv
    #
    cr
    wcel
    #
    wa
    #
    cR
    @0
    crest
    co
    #
    cS
    @0
    crest
    co
    #
    vx
    cv
    cF
    cfv
    @2
    clt
    wbr
    vx
    @0
    crab
    wph
    @5
    @6
    wss
    #
    @3
    wph
    cS
    csalg
    wcel
    cR
    cS
    wss
    @7
    smfsssmf.s
    smfsssmf.i
    @0
    cR
    cS
    csalg
    ssrest
    syl2anc
    adantr
    @4
    vx
    @2
    @0
    cR
    cF
    wph
    cR
    csalg
    wcel
    @3
    smfsssmf.r
    adantr
    wph
    cF
    cR
    csmblfn
    cfv
    wcel
    @3
    smfsssmf.f
    adantr
    @1
    wph
    @3
    simpr
    smfpreimalt
    sseldd
    issmfd
end
