include "ceupth.mm"
include "cfv.mm"
include "wbr.mm"
include "cwlks.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cdm.mm"
include "wf1o.mm"
include "wa.mm"
include "iseupthf1o.mm"
include "biimpi.mm"

theorem eupthi
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  assume eupths.i: |- I = ( iEdg ` G )


  assert |- ( F ( EulerPaths ` G ) P -> ( F ( Walks ` G ) P /\ F : ( 0 ..^ ( # ` F ) ) -1-1-onto-> dom I ) )

  proof
    cF
    cP
    cG
    ceupth
    cfv
    wbr
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    cc0
    cF
    chash
    cfv
    cfzo
    co
    cI
    cdm
    cF
    wf1o
    wa
    cP
    cF
    cG
    cI
    eupths.i
    iseupthf1o
    biimpi
end
