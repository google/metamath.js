include "cid.mm"
include "cres.mm"
include "cmpt.mm"
include "weq.mm"
include "eqidd.mm"
include "cbvmptv.mm"
include "eqtri.mm"

theorem tendo0cbv
  let cB: class B
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cO: class O
  assume tendo0cbv.o: |- O = ( f e. T |-> ( _I |` B ) )

  disjoint B f
  disjoint B g
  disjoint T f
  disjoint T g
  assert |- O = ( g e. T |-> ( _I |` B ) )

  proof
    cO
    vf
    cT
    cid
    cB
    cres
    #
    cmpt
    vg
    cT
    @0
    cmpt
    tendo0cbv.o
    vf
    vg
    cT
    @0
    @0
    vf
    vg
    weq
    @0
    eqidd
    cbvmptv
    eqtri
end
