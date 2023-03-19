include "co.mm"
include "cin.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "lsmdisj2b.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "lsmcom2.mm"
include "syl3anc.mm"
include "ineq2d.mm"
include "eqeq1d.mm"
include "incom.mm"
include "a1i.mm"
include "anbi12d.mm"
include "bitr4d.mm"

theorem lsmdisj3b
  let wph: wff ph
  let c.po: class .(+)
  let cS: class S
  let cT: class T
  let cU: class U
  let cG: class G
  let c.0: class .0.
  let cZ: class Z
  let vx: setvar x
  let vs: setvar s
  let vu: setvar u
  assume lsmcntz.p: |- .(+) = ( LSSum ` G )
  assume lsmcntz.s: |- ( ph -> S e. ( SubGrp ` G ) )
  assume lsmcntz.t: |- ( ph -> T e. ( SubGrp ` G ) )
  assume lsmcntz.u: |- ( ph -> U e. ( SubGrp ` G ) )
  assume lsmdisj.o: |- .0. = ( 0g ` G )
  assume lsmdisj3b.z: |- Z = ( Cntz ` G )
  assume lsmdisj3b.2: |- ( ph -> T C_ ( Z ` U ) )


  assert |- ( ph -> ( ( ( ( S .(+) T ) i^i U ) = { .0. } /\ ( S i^i T ) = { .0. } ) <-> ( ( S i^i ( T .(+) U ) ) = { .0. } /\ ( T i^i U ) = { .0. } ) ) )

  proof
    wph
    cS
    cT
    c.po
    co
    cU
    cin
    c.0
    csn
    #
    wceq
    cS
    cT
    cin
    @0
    wceq
    wa
    cS
    cU
    cT
    c.po
    co
    #
    cin
    #
    @0
    wceq
    #
    cU
    cT
    cin
    #
    @0
    wceq
    #
    wa
    cS
    cT
    cU
    c.po
    co
    #
    cin
    #
    @0
    wceq
    #
    cT
    cU
    cin
    #
    @0
    wceq
    #
    wa
    wph
    c.po
    cS
    cU
    cT
    cG
    c.0
    lsmcntz.p
    lsmcntz.s
    lsmcntz.u
    lsmcntz.t
    lsmdisj.o
    lsmdisj2b
    wph
    @8
    @3
    @10
    @5
    wph
    @7
    @2
    @0
    wph
    @6
    @1
    cS
    wph
    cT
    cG
    csubg
    cfv
    #
    wcel
    cU
    @11
    wcel
    cT
    cU
    cZ
    cfv
    wss
    @6
    @1
    wceq
    lsmcntz.t
    lsmcntz.u
    lsmdisj3b.2
    c.po
    cT
    cU
    cG
    cZ
    lsmcntz.p
    lsmdisj3b.z
    lsmcom2
    syl3anc
    ineq2d
    eqeq1d
    wph
    @9
    @4
    @0
    @9
    @4
    wceq
    wph
    cT
    cU
    incom
    a1i
    eqeq1d
    anbi12d
    bitr4d
end
