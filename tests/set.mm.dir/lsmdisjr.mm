include "cin.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "co.mm"
include "incom.mm"
include "syl5eqr.mm"
include "lsmdisj.mm"
include "eqeq1i.mm"
include "anbi12i.mm"
include "sylib.mm"

theorem lsmdisjr
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
  assume lsmdisjr.i: |- ( ph -> ( S i^i ( T .(+) U ) ) = { .0. } )


  assert |- ( ph -> ( ( S i^i T ) = { .0. } /\ ( S i^i U ) = { .0. } ) )

  proof
    wph
    cT
    cS
    cin
    #
    c.0
    csn
    #
    wceq
    #
    cU
    cS
    cin
    #
    @1
    wceq
    #
    wa
    cS
    cT
    cin
    #
    @1
    wceq
    #
    cS
    cU
    cin
    #
    @1
    wceq
    #
    wa
    wph
    c.po
    cT
    cU
    cS
    cG
    c.0
    lsmcntz.p
    lsmcntz.t
    lsmcntz.u
    lsmcntz.s
    lsmdisj.o
    wph
    cT
    cU
    c.po
    co
    #
    cS
    cin
    cS
    @9
    cin
    @1
    cS
    @9
    incom
    lsmdisjr.i
    syl5eqr
    lsmdisj
    @2
    @6
    @4
    @8
    @0
    @5
    @1
    cT
    cS
    incom
    eqeq1i
    @3
    @7
    @1
    cU
    cS
    incom
    eqeq1i
    anbi12i
    sylib
end
