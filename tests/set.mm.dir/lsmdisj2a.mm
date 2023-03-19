include "co.mm"
include "cin.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "lsmdisj2.mm"
include "lsmdisj.mm"
include "simpld.mm"
include "jca.mm"
include "incom.mm"
include "syl5eq.mm"
include "lsmdisjr.mm"
include "impbida.mm"

theorem lsmdisj2a
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


  assert |- ( ph -> ( ( ( ( S .(+) T ) i^i U ) = { .0. } /\ ( S i^i T ) = { .0. } ) <-> ( ( T i^i ( S .(+) U ) ) = { .0. } /\ ( S i^i U ) = { .0. } ) ) )

  proof
    wph
    cS
    cT
    c.po
    co
    #
    cU
    cin
    #
    c.0
    csn
    #
    wceq
    #
    cS
    cT
    cin
    #
    @2
    wceq
    #
    wa
    #
    cT
    cS
    cU
    c.po
    co
    #
    cin
    #
    @2
    wceq
    #
    cS
    cU
    cin
    @2
    wceq
    #
    wa
    #
    wph
    @6
    wa
    #
    @9
    @10
    @12
    c.po
    cS
    cT
    cU
    cG
    c.0
    lsmcntz.p
    wph
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    @6
    lsmcntz.s
    adantr
    #
    wph
    cT
    @13
    wcel
    #
    @6
    lsmcntz.t
    adantr
    #
    wph
    cU
    @13
    wcel
    #
    @6
    lsmcntz.u
    adantr
    #
    lsmdisj.o
    wph
    @3
    @5
    simprl
    #
    wph
    @3
    @5
    simprr
    lsmdisj2
    @12
    @10
    cT
    cU
    cin
    @2
    wceq
    #
    @12
    c.po
    cS
    cT
    cU
    cG
    c.0
    lsmcntz.p
    @15
    @17
    @19
    lsmdisj.o
    @20
    lsmdisj
    simpld
    jca
    wph
    @11
    wa
    #
    @3
    @5
    @22
    @1
    cU
    @0
    cin
    @2
    @0
    cU
    incom
    @22
    c.po
    cS
    cU
    cT
    cG
    c.0
    lsmcntz.p
    wph
    @14
    @11
    lsmcntz.s
    adantr
    #
    wph
    @18
    @11
    lsmcntz.u
    adantr
    #
    wph
    @16
    @11
    lsmcntz.t
    adantr
    #
    lsmdisj.o
    @22
    @7
    cT
    cin
    @8
    @2
    @7
    cT
    incom
    wph
    @9
    @10
    simprl
    #
    syl5eq
    wph
    @9
    @10
    simprr
    lsmdisj2
    syl5eq
    @22
    @4
    cT
    cS
    cin
    #
    @2
    cS
    cT
    incom
    @22
    @27
    @2
    wceq
    @21
    @22
    c.po
    cT
    cS
    cU
    cG
    c.0
    lsmcntz.p
    @25
    @23
    @24
    lsmdisj.o
    @26
    lsmdisjr
    simpld
    syl5eq
    jca
    impbida
end
