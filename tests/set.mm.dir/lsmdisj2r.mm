include "co.mm"
include "cin.mm"
include "coppg.mm"
include "cfv.mm"
include "clsm.mm"
include "csn.mm"
include "eqid.mm"
include "oppglsm.mm"
include "ineq2i.mm"
include "incom.mm"
include "eqtri.mm"
include "csubg.mm"
include "oppgsubg.mm"
include "syl6eleq.mm"
include "oppgid.mm"
include "ineq1i.mm"
include "syl5eq.mm"
include "syl5eqr.mm"
include "lsmdisj2.mm"

theorem lsmdisj2r
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
  assume lsmdisj2r.i: |- ( ph -> ( T i^i U ) = { .0. } )


  assert |- ( ph -> ( ( S .(+) U ) i^i T ) = { .0. } )

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
    cT
    cU
    cS
    cG
    coppg
    cfv
    #
    clsm
    cfv
    #
    co
    #
    cin
    #
    c.0
    csn
    #
    @5
    cT
    @0
    cin
    @1
    @4
    @0
    cT
    c.po
    cU
    cS
    cG
    @2
    @2
    eqid
    #
    lsmcntz.p
    oppglsm
    ineq2i
    cT
    @0
    incom
    eqtri
    wph
    @3
    cU
    cT
    cS
    @2
    c.0
    @3
    eqid
    wph
    cU
    cG
    csubg
    cfv
    #
    @2
    csubg
    cfv
    #
    lsmcntz.u
    cG
    @2
    @7
    oppgsubg
    #
    syl6eleq
    wph
    cT
    @8
    @9
    lsmcntz.t
    @10
    syl6eleq
    wph
    cS
    @8
    @9
    lsmcntz.s
    @10
    syl6eleq
    cG
    @2
    c.0
    @7
    lsmdisj.o
    oppgid
    wph
    cU
    cT
    @3
    co
    #
    cS
    cin
    #
    cS
    cT
    cU
    c.po
    co
    #
    cin
    #
    @6
    @12
    @13
    cS
    cin
    @14
    @11
    @13
    cS
    c.po
    cU
    cT
    cG
    @2
    @7
    lsmcntz.p
    oppglsm
    ineq1i
    @13
    cS
    incom
    eqtri
    lsmdisjr.i
    syl5eq
    wph
    cU
    cT
    cin
    cT
    cU
    cin
    @6
    cT
    cU
    incom
    lsmdisj2r.i
    syl5eqr
    lsmdisj2
    syl5eqr
end
