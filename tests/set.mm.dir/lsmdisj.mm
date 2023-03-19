include "cin.mm"
include "csn.mm"
include "wceq.mm"
include "co.mm"
include "wss.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "lsmub1.mm"
include "syl2anc.mm"
include "ssrin.mm"
include "syl.mm"
include "sseqtrd.mm"
include "subg0cl.mm"
include "elind.mm"
include "snssd.mm"
include "eqssd.mm"
include "lsmub2.mm"
include "jca.mm"

theorem lsmdisj
  let wph: wff ph
  let c.po: class .(+)
  let cS: class S
  let cT: class T
  let cU: class U
  let cG: class G
  let c.0: class .0.
  let vx: setvar x
  let vs: setvar s
  let vu: setvar u
  assume lsmcntz.p: |- .(+) = ( LSSum ` G )
  assume lsmcntz.s: |- ( ph -> S e. ( SubGrp ` G ) )
  assume lsmcntz.t: |- ( ph -> T e. ( SubGrp ` G ) )
  assume lsmcntz.u: |- ( ph -> U e. ( SubGrp ` G ) )
  assume lsmdisj.o: |- .0. = ( 0g ` G )
  assume lsmdisj.i: |- ( ph -> ( ( S .(+) T ) i^i U ) = { .0. } )


  assert |- ( ph -> ( ( S i^i U ) = { .0. } /\ ( T i^i U ) = { .0. } ) )

  proof
    wph
    cS
    cU
    cin
    #
    c.0
    csn
    #
    wceq
    cT
    cU
    cin
    #
    @1
    wceq
    wph
    @0
    @1
    wph
    @0
    cS
    cT
    c.po
    co
    #
    cU
    cin
    #
    @1
    wph
    cS
    @3
    wss
    #
    @0
    @4
    wss
    wph
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    cT
    @6
    wcel
    #
    @5
    lsmcntz.s
    lsmcntz.t
    c.po
    cS
    cT
    cG
    lsmcntz.p
    lsmub1
    syl2anc
    cS
    @3
    cU
    ssrin
    syl
    lsmdisj.i
    sseqtrd
    wph
    c.0
    @0
    wph
    cS
    cU
    c.0
    wph
    @7
    c.0
    cS
    wcel
    lsmcntz.s
    cS
    cG
    c.0
    lsmdisj.o
    subg0cl
    syl
    wph
    cU
    @6
    wcel
    c.0
    cU
    wcel
    lsmcntz.u
    cU
    cG
    c.0
    lsmdisj.o
    subg0cl
    syl
    #
    elind
    snssd
    eqssd
    wph
    @2
    @1
    wph
    @2
    @4
    @1
    wph
    cT
    @3
    wss
    #
    @2
    @4
    wss
    wph
    @7
    @8
    @10
    lsmcntz.s
    lsmcntz.t
    c.po
    cS
    cT
    cG
    lsmcntz.p
    lsmub2
    syl2anc
    cT
    @3
    cU
    ssrin
    syl
    lsmdisj.i
    sseqtrd
    wph
    c.0
    @2
    wph
    cT
    cU
    c.0
    wph
    @8
    c.0
    cT
    wcel
    lsmcntz.t
    cT
    cG
    c.0
    lsmdisj.o
    subg0cl
    syl
    @9
    elind
    snssd
    eqssd
    jca
end
