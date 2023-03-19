include "cc0.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "cdm.mm"
include "wfo.mm"
include "ceupth.mm"
include "ctrls.mm"
include "eupths.mm"
include "wceq.mm"
include "wa.mm"
include "simpl.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "adantr.mm"
include "eqidd.mm"
include "foeq123d.mm"
include "reltrls.mm"
include "brfvopabrbr.mm"

theorem iseupth
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  assume eupths.i: |- I = ( iEdg ` G )


  assert |- ( F ( EulerPaths ` G ) P <-> ( F ( Trails ` G ) P /\ F : ( 0 ..^ ( # ` F ) ) -onto-> dom I ) )

  proof
    cc0
    vf
    cv
    #
    chash
    cfv
    #
    cfzo
    co
    #
    cI
    cdm
    #
    @0
    wfo
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    @3
    cF
    wfo
    vf
    vp
    ceupth
    ctrls
    cF
    cP
    cG
    vf
    cG
    cI
    vp
    eupths.i
    eupths
    @0
    cF
    wceq
    #
    vp
    cv
    cP
    wceq
    #
    wa
    #
    @2
    @5
    @3
    @3
    @0
    cF
    @6
    @7
    simpl
    @6
    @2
    @5
    wceq
    @7
    @6
    @1
    @4
    cc0
    cfzo
    @0
    cF
    chash
    fveq2
    oveq2d
    adantr
    @8
    @3
    eqidd
    foeq123d
    cG
    reltrls
    brfvopabrbr
end
