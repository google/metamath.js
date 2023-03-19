include "cof.mm"
include "co.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "ovex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "wcel.mm"
include "wa.mm"
include "eqidd.mm"
include "offval.mm"
include "fneq1d.mm"
include "mpbiri.mm"

theorem offn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  let cX: class X
  assume offval.1: |- ( ph -> F Fn A )
  assume offval.2: |- ( ph -> G Fn B )
  assume offval.3: |- ( ph -> A e. V )
  assume offval.4: |- ( ph -> B e. W )
  assume offval.5: |- ( A i^i B ) = S


  assert |- ( ph -> ( F oF R G ) Fn S )

  proof
    wph
    cF
    cG
    cR
    cof
    co
    #
    cS
    wfn
    vx
    cS
    vx
    cv
    #
    cF
    cfv
    #
    @1
    cG
    cfv
    #
    cR
    co
    #
    cmpt
    #
    cS
    wfn
    vx
    cS
    @4
    @5
    @2
    @3
    cR
    ovex
    @5
    eqid
    fnmpti
    wph
    cS
    @0
    @5
    wph
    vx
    cA
    cB
    @2
    @3
    cR
    cS
    cF
    cG
    cV
    cW
    offval.1
    offval.2
    offval.3
    offval.4
    offval.5
    wph
    @1
    cA
    wcel
    wa
    @2
    eqidd
    wph
    @1
    cB
    wcel
    wa
    @3
    eqidd
    offval
    fneq1d
    mpbiri
end
