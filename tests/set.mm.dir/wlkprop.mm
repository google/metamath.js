include "cvv.mm"
include "wcel.mm"
include "w3a.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cdm.mm"
include "cword.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "cfzo.mm"
include "wral.mm"
include "wksfval.mm"
include "brfvopab.mm"
include "iswlk.mm"
include "biimpd.mm"
include "mpcom.mm"

theorem wlkprop
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  let cW: class W
  assume wksfval.v: |- V = ( Vtx ` G )
  assume wksfval.i: |- I = ( iEdg ` G )

  disjoint G k
  disjoint F k
  disjoint P k
  disjoint G f
  disjoint G g
  disjoint G p
  disjoint f g
  disjoint f k
  disjoint f p
  disjoint g k
  disjoint g p
  disjoint k p
  disjoint I f
  disjoint I g
  disjoint I p
  disjoint V g
  disjoint V p
  disjoint W f
  disjoint W g
  disjoint F f
  disjoint F p
  disjoint P f
  disjoint P p
  disjoint V f
  assert |- ( F ( Walks ` G ) P -> ( F e. Word dom I /\ P : ( 0 ... ( # ` F ) ) --> V /\ A. k e. ( 0 ..^ ( # ` F ) ) if- ( ( P ` k ) = ( P ` ( k + 1 ) ) , ( I ` ( F ` k ) ) = { ( P ` k ) } , { ( P ` k ) , ( P ` ( k + 1 ) ) } C_ ( I ` ( F ` k ) ) ) ) )

  proof
    cG
    cvv
    wcel
    cF
    cvv
    wcel
    cP
    cvv
    wcel
    w3a
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cF
    cI
    cdm
    cword
    #
    wcel
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    cV
    cP
    wf
    vk
    cv
    #
    cP
    cfv
    #
    @4
    c1
    caddc
    co
    #
    cP
    cfv
    #
    wceq
    @4
    cF
    cfv
    cI
    cfv
    #
    @5
    csn
    wceq
    @5
    @7
    cpr
    @8
    wss
    wif
    vk
    cc0
    @3
    cfzo
    co
    wral
    w3a
    #
    vf
    cv
    #
    @2
    wcel
    cc0
    @10
    chash
    cfv
    #
    cfz
    co
    cV
    vp
    cv
    #
    wf
    @4
    @12
    cfv
    #
    @6
    @12
    cfv
    #
    wceq
    @4
    @10
    cfv
    cI
    cfv
    #
    @13
    csn
    wceq
    @13
    @14
    cpr
    @15
    wss
    wif
    vk
    cc0
    @11
    cfzo
    co
    wral
    w3a
    vf
    vp
    cF
    cP
    cwlks
    cG
    vf
    vk
    cG
    cI
    cV
    cvv
    vp
    wksfval.v
    wksfval.i
    wksfval
    brfvopab
    @0
    @1
    @9
    cP
    cvv
    vk
    cF
    cG
    cI
    cV
    cvv
    cvv
    wksfval.v
    wksfval.i
    iswlk
    biimpd
    mpcom
end
