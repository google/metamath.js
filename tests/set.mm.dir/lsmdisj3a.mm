include "co.mm"
include "cin.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "lsmcom2.mm"
include "syl3anc.mm"
include "ineq1d.mm"
include "eqeq1d.mm"
include "incom.mm"
include "a1i.mm"
include "anbi12d.mm"
include "lsmdisj2a.mm"
include "bitrd.mm"

theorem lsmdisj3a
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
  assume lsmdisj3a.2: |- ( ph -> S C_ ( Z ` T ) )


  assert |- ( ph -> ( ( ( ( S .(+) T ) i^i U ) = { .0. } /\ ( S i^i T ) = { .0. } ) <-> ( ( S i^i ( T .(+) U ) ) = { .0. } /\ ( T i^i U ) = { .0. } ) ) )

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
    cT
    cS
    c.po
    co
    #
    cU
    cin
    #
    @2
    wceq
    #
    cT
    cS
    cin
    #
    @2
    wceq
    #
    wa
    cS
    cT
    cU
    c.po
    co
    cin
    @2
    wceq
    cT
    cU
    cin
    @2
    wceq
    wa
    wph
    @3
    @8
    @5
    @10
    wph
    @1
    @7
    @2
    wph
    @0
    @6
    cU
    wph
    cS
    cG
    csubg
    cfv
    #
    wcel
    cT
    @11
    wcel
    cS
    cT
    cZ
    cfv
    wss
    @0
    @6
    wceq
    lsmcntz.s
    lsmcntz.t
    lsmdisj3a.2
    c.po
    cS
    cT
    cG
    cZ
    lsmcntz.p
    lsmdisj3b.z
    lsmcom2
    syl3anc
    ineq1d
    eqeq1d
    wph
    @4
    @9
    @2
    @4
    @9
    wceq
    wph
    cS
    cT
    incom
    a1i
    eqeq1d
    anbi12d
    wph
    c.po
    cT
    cS
    cU
    cG
    c.0
    lsmcntz.p
    lsmcntz.t
    lsmcntz.s
    lsmcntz.u
    lsmdisj.o
    lsmdisj2a
    bitrd
end
