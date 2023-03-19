include "co.mm"
include "cin.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "incom.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "adantr.mm"
include "simprl.mm"
include "syl5eq.mm"
include "simprr.mm"
include "lsmdisj2r.mm"
include "lsmdisj.mm"
include "simprd.mm"
include "jca.mm"
include "lsmdisjr.mm"
include "impbida.mm"

theorem lsmdisj2b
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


  assert |- ( ph -> ( ( ( ( S .(+) U ) i^i T ) = { .0. } /\ ( S i^i U ) = { .0. } ) <-> ( ( S i^i ( T .(+) U ) ) = { .0. } /\ ( T i^i U ) = { .0. } ) ) )

  proof
    wph
    cS
    cU
    c.po
    co
    #
    cT
    cin
    #
    c.0
    csn
    #
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
    cS
    cT
    cU
    c.po
    co
    #
    cin
    #
    @2
    wceq
    #
    cT
    cU
    cin
    #
    @2
    wceq
    #
    wa
    #
    wph
    @5
    wa
    #
    @8
    @10
    @12
    @7
    @6
    cS
    cin
    @2
    cS
    @6
    incom
    @12
    c.po
    cT
    cS
    cU
    cG
    c.0
    lsmcntz.p
    wph
    cT
    cG
    csubg
    cfv
    #
    wcel
    #
    @5
    lsmcntz.t
    adantr
    #
    wph
    cS
    @13
    wcel
    #
    @5
    lsmcntz.s
    adantr
    #
    wph
    cU
    @13
    wcel
    #
    @5
    lsmcntz.u
    adantr
    #
    lsmdisj.o
    @12
    cT
    @0
    cin
    @1
    @2
    cT
    @0
    incom
    wph
    @3
    @4
    simprl
    #
    syl5eq
    wph
    @3
    @4
    simprr
    lsmdisj2r
    syl5eq
    @12
    @9
    cU
    cT
    cin
    #
    @2
    cT
    cU
    incom
    @12
    cS
    cT
    cin
    @2
    wceq
    #
    @21
    @2
    wceq
    @12
    c.po
    cS
    cU
    cT
    cG
    c.0
    lsmcntz.p
    @17
    @19
    @15
    lsmdisj.o
    @20
    lsmdisj
    simprd
    syl5eq
    jca
    wph
    @11
    wa
    #
    @3
    @4
    @23
    c.po
    cS
    cT
    cU
    cG
    c.0
    lsmcntz.p
    wph
    @16
    @11
    lsmcntz.s
    adantr
    #
    wph
    @14
    @11
    lsmcntz.t
    adantr
    #
    wph
    @18
    @11
    lsmcntz.u
    adantr
    #
    lsmdisj.o
    wph
    @8
    @10
    simprl
    #
    wph
    @8
    @10
    simprr
    lsmdisj2r
    @23
    @22
    @4
    @23
    c.po
    cS
    cT
    cU
    cG
    c.0
    lsmcntz.p
    @24
    @25
    @26
    lsmdisj.o
    @27
    lsmdisjr
    simprd
    jca
    impbida
end
