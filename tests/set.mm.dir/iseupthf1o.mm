include "ceupth.mm"
include "cfv.mm"
include "wbr.mm"
include "ctrls.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cdm.mm"
include "wfo.mm"
include "wa.mm"
include "cwlks.mm"
include "ccnv.mm"
include "wfun.mm"
include "wf1o.mm"
include "iseupth.mm"
include "istrl.mm"
include "anbi1i.mm"
include "anass.mm"
include "ancom.mm"
include "anbi2i.mm"
include "3bitri.mm"
include "dff1o3.mm"
include "bicomi.mm"

theorem iseupthf1o
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  assume eupths.i: |- I = ( iEdg ` G )


  assert |- ( F ( EulerPaths ` G ) P <-> ( F ( Walks ` G ) P /\ F : ( 0 ..^ ( # ` F ) ) -1-1-onto-> dom I ) )

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
    ctrls
    cfv
    wbr
    #
    cc0
    cF
    chash
    cfv
    cfzo
    co
    #
    cI
    cdm
    #
    cF
    wfo
    #
    wa
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    @3
    cF
    ccnv
    wfun
    #
    wa
    #
    wa
    #
    @5
    @1
    @2
    cF
    wf1o
    #
    wa
    cP
    cF
    cG
    cI
    eupths.i
    iseupth
    @4
    @5
    @6
    wa
    #
    @3
    wa
    @5
    @6
    @3
    wa
    #
    wa
    @8
    @0
    @10
    @3
    cP
    cF
    cG
    istrl
    anbi1i
    @5
    @6
    @3
    anass
    @11
    @7
    @5
    @6
    @3
    ancom
    anbi2i
    3bitri
    @7
    @9
    @5
    @9
    @7
    @1
    @2
    cF
    dff1o3
    bicomi
    anbi2i
    3bitri
end
