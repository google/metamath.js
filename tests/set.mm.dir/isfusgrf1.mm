include "cfusgr.mm"
include "wcel.mm"
include "cusgr.mm"
include "cfn.mm"
include "wa.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "wf1.mm"
include "isfusgr.mm"
include "isusgrs.mm"
include "anbi1d.mm"
include "syl5bb.mm"

theorem isfusgrf1
  let vx: setvar x
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let vg: setvar g
  assume isfusgr.v: |- V = ( Vtx ` G )
  assume isfusgrf1.i: |- I = ( iEdg ` G )

  disjoint G x
  disjoint V x
  disjoint W x
  disjoint G g
  disjoint V g
  assert |- ( G e. W -> ( G e. FinUSGraph <-> ( I : dom I -1-1-> { x e. ~P V | ( # ` x ) = 2 } /\ V e. Fin ) ) )

  proof
    cG
    cfusgr
    wcel
    cG
    cusgr
    wcel
    #
    cV
    cfn
    wcel
    #
    wa
    cG
    cW
    wcel
    #
    cI
    cdm
    vx
    cv
    chash
    cfv
    c2
    wceq
    vx
    cV
    cpw
    crab
    cI
    wf1
    #
    @1
    wa
    cG
    cV
    isfusgr.v
    isfusgr
    @2
    @0
    @3
    @1
    vx
    cW
    cI
    cG
    cV
    isfusgr.v
    isfusgrf1.i
    isusgrs
    anbi1d
    syl5bb
end
