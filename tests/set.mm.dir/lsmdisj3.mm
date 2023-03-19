include "co.mm"
include "cin.mm"
include "csn.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wceq.mm"
include "lsmcom2.mm"
include "syl3anc.mm"
include "ineq1d.mm"
include "eqtr3d.mm"
include "incom.mm"
include "syl5eq.mm"
include "lsmdisj2.mm"

theorem lsmdisj3
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
  assume lsmdisj.i: |- ( ph -> ( ( S .(+) T ) i^i U ) = { .0. } )
  assume lsmdisj2.i: |- ( ph -> ( S i^i T ) = { .0. } )
  assume lsmdisj3.z: |- Z = ( Cntz ` G )
  assume lsmdisj3.s: |- ( ph -> S C_ ( Z ` T ) )


  assert |- ( ph -> ( S i^i ( T .(+) U ) ) = { .0. } )

  proof
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
    wph
    cS
    cT
    c.po
    co
    #
    cU
    cin
    cT
    cS
    c.po
    co
    #
    cU
    cin
    c.0
    csn
    #
    wph
    @0
    @1
    cU
    wph
    cS
    cG
    csubg
    cfv
    #
    wcel
    cT
    @3
    wcel
    cS
    cT
    cZ
    cfv
    wss
    @0
    @1
    wceq
    lsmcntz.s
    lsmcntz.t
    lsmdisj3.s
    c.po
    cS
    cT
    cG
    cZ
    lsmcntz.p
    lsmdisj3.z
    lsmcom2
    syl3anc
    ineq1d
    lsmdisj.i
    eqtr3d
    wph
    cT
    cS
    cin
    cS
    cT
    cin
    @2
    cT
    cS
    incom
    lsmdisj2.i
    syl5eq
    lsmdisj2
end
