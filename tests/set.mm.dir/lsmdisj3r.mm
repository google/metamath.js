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
include "ineq2d.mm"
include "eqtr3d.mm"
include "incom.mm"
include "syl5eq.mm"
include "lsmdisj2r.mm"

theorem lsmdisj3r
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
  assume lsmdisjr.i: |- ( ph -> ( S i^i ( T .(+) U ) ) = { .0. } )
  assume lsmdisj2r.i: |- ( ph -> ( T i^i U ) = { .0. } )
  assume lsmdisj3r.z: |- Z = ( Cntz ` G )
  assume lsmdisj3r.s: |- ( ph -> T C_ ( Z ` U ) )


  assert |- ( ph -> ( ( S .(+) T ) i^i U ) = { .0. } )

  proof
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
    wph
    cS
    cT
    cU
    c.po
    co
    #
    cin
    cS
    cU
    cT
    c.po
    co
    #
    cin
    c.0
    csn
    #
    wph
    @0
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
    @3
    wcel
    cT
    cU
    cZ
    cfv
    wss
    @0
    @1
    wceq
    lsmcntz.t
    lsmcntz.u
    lsmdisj3r.s
    c.po
    cT
    cU
    cG
    cZ
    lsmcntz.p
    lsmdisj3r.z
    lsmcom2
    syl3anc
    ineq2d
    lsmdisjr.i
    eqtr3d
    wph
    cU
    cT
    cin
    cT
    cU
    cin
    @2
    cU
    cT
    incom
    lsmdisj2r.i
    syl5eq
    lsmdisj2r
end
