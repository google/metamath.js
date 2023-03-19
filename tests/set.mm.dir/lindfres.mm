include "clmod.mm"
include "wcel.mm"
include "clindf.mm"
include "wbr.mm"
include "wa.mm"
include "cres.mm"
include "cid.mm"
include "cdm.mm"
include "ccom.mm"
include "coires1.mm"
include "resdmres.mm"
include "eqtri.mm"
include "wf1.mm"
include "wss.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of1.mm"
include "ax-mp.mm"
include "resss.mm"
include "dmss.mm"
include "f1ss.mm"
include "mp2an.mm"
include "f1lindf.mm"
include "mp3an3.mm"
include "syl5eqbrr.mm"

theorem lindfres
  let cF: class F
  let cW: class W
  let cX: class X


  assert |- ( ( W e. LMod /\ F LIndF W ) -> ( F |` X ) LIndF W )

  proof
    cW
    clmod
    wcel
    #
    cF
    cW
    clindf
    wbr
    #
    wa
    cF
    cX
    cres
    #
    cF
    cid
    @2
    cdm
    #
    cres
    #
    ccom
    #
    cW
    clindf
    @5
    cF
    @3
    cres
    @2
    cF
    @3
    coires1
    cF
    cX
    resdmres
    eqtri
    @0
    @1
    @3
    cF
    cdm
    #
    @4
    wf1
    #
    @5
    cW
    clindf
    wbr
    @3
    @3
    @4
    wf1
    #
    @3
    @6
    wss
    #
    @7
    @3
    @3
    @4
    wf1o
    @8
    @3
    f1oi
    @3
    @3
    @4
    f1of1
    ax-mp
    @2
    cF
    wss
    @9
    cF
    cX
    resss
    @2
    cF
    dmss
    ax-mp
    @3
    @3
    @6
    @4
    f1ss
    mp2an
    cF
    @4
    @3
    cW
    f1lindf
    mp3an3
    syl5eqbrr
end
