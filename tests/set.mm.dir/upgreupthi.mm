include "cupgr.mm"
include "wcel.mm"
include "ceupth.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cdm.mm"
include "wf1o.mm"
include "cfz.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "upgriseupth.mm"
include "biimpa.mm"

theorem upgreupthi
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  let cN: class N
  assume eupths.i: |- I = ( iEdg ` G )
  assume upgriseupth.v: |- V = ( Vtx ` G )

  disjoint F k
  disjoint G k
  disjoint I k
  disjoint P k
  disjoint V k
  disjoint G f
  disjoint G g
  disjoint G p
  disjoint f g
  disjoint f p
  disjoint g p
  disjoint I g
  disjoint F f
  disjoint F p
  disjoint I f
  disjoint I p
  disjoint P f
  disjoint P p
  disjoint N k
  assert |- ( ( G e. UPGraph /\ F ( EulerPaths ` G ) P ) -> ( F : ( 0 ..^ ( # ` F ) ) -1-1-onto-> dom I /\ P : ( 0 ... ( # ` F ) ) --> V /\ A. k e. ( 0 ..^ ( # ` F ) ) ( I ` ( F ` k ) ) = { ( P ` k ) , ( P ` ( k + 1 ) ) } ) )

  proof
    cG
    cupgr
    wcel
    cF
    cP
    cG
    ceupth
    cfv
    wbr
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    cI
    cdm
    cF
    wf1o
    cc0
    @0
    cfz
    co
    cV
    cP
    wf
    vk
    cv
    #
    cF
    cfv
    cI
    cfv
    @2
    cP
    cfv
    @2
    c1
    caddc
    co
    cP
    cfv
    cpr
    wceq
    vk
    @1
    wral
    w3a
    cP
    vk
    cF
    cG
    cI
    cV
    eupths.i
    upgriseupth.v
    upgriseupth
    biimpa
end
