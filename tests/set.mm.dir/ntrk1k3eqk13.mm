include "cv.mm"
include "cin.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "cpw.mm"
include "wral.mm"
include "wceq.mm"
include "wi.mm"
include "r19.26-2.mm"
include "eqss.mm"
include "2ralbii.mm"
include "isotone2.mm"
include "anbi1i.mm"
include "3bitr4ri.mm"

theorem ntrk1k3eqk13
  let vt: setvar t
  let cB: class B
  let cI: class I
  let vs: setvar s

  disjoint B s
  disjoint B t
  disjoint s t
  disjoint I s
  disjoint I t
  assert |- ( ( A. s e. ~P B A. t e. ~P B ( s C_ t -> ( I ` s ) C_ ( I ` t ) ) /\ A. s e. ~P B A. t e. ~P B ( ( I ` s ) i^i ( I ` t ) ) C_ ( I ` ( s i^i t ) ) ) <-> A. s e. ~P B A. t e. ~P B ( I ` ( s i^i t ) ) = ( ( I ` s ) i^i ( I ` t ) ) )

  proof
    vs
    cv
    #
    vt
    cv
    #
    cin
    cI
    cfv
    #
    @0
    cI
    cfv
    #
    @1
    cI
    cfv
    #
    cin
    #
    wss
    #
    @5
    @2
    wss
    #
    wa
    #
    vt
    cB
    cpw
    #
    wral
    vs
    @9
    wral
    @6
    vt
    @9
    wral
    vs
    @9
    wral
    #
    @7
    vt
    @9
    wral
    vs
    @9
    wral
    #
    wa
    @2
    @5
    wceq
    #
    vt
    @9
    wral
    vs
    @9
    wral
    @0
    @1
    wss
    @3
    @4
    wss
    wi
    vt
    @9
    wral
    vs
    @9
    wral
    #
    @11
    wa
    @6
    @7
    vs
    vt
    @9
    @9
    r19.26-2
    @12
    @8
    vs
    vt
    @9
    @9
    @2
    @5
    eqss
    2ralbii
    @13
    @10
    @11
    cB
    cI
    vs
    vt
    isotone2
    anbi1i
    3bitr4ri
end
