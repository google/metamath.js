include "wcel.mm"
include "cvv.mm"
include "w3a.mm"
include "cupwlks.mm"
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
include "cpr.mm"
include "wceq.mm"
include "cfzo.mm"
include "wral.mm"
include "wi.mm"
include "upwlksfval.mm"
include "brfvopab.mm"
include "a1i.mm"
include "wa.mm"
include "elex.mm"
include "cpm.mm"
include "ovex.mm"
include "cvtx.mm"
include "fvexi.mm"
include "fpm.mm"
include "elexd.mm"
include "anim12i.mm"
include "3adant3.mm"
include "ex.mm"
include "3anass.mm"
include "syl6ibr.mm"
include "wb.mm"
include "isupwlk.mm"
include "pm5.21ndd.mm"

theorem isupwlkg
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  let vx: setvar x
  assume upwlksfval.v: |- V = ( Vtx ` G )
  assume upwlksfval.i: |- I = ( iEdg ` G )

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
  disjoint k x
  assert |- ( G e. W -> ( F ( UPWalks ` G ) P <-> ( F e. Word dom I /\ P : ( 0 ... ( # ` F ) ) --> V /\ A. k e. ( 0 ..^ ( # ` F ) ) ( I ` ( F ` k ) ) = { ( P ` k ) , ( P ` ( k + 1 ) ) } ) ) )

  proof
    cG
    cW
    wcel
    #
    cG
    cvv
    wcel
    #
    cF
    cvv
    wcel
    #
    cP
    cvv
    wcel
    #
    w3a
    #
    cF
    cP
    cG
    cupwlks
    cfv
    wbr
    #
    cF
    cI
    cdm
    cword
    #
    wcel
    #
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    #
    cV
    cP
    wf
    #
    vk
    cv
    #
    cF
    cfv
    cI
    cfv
    @11
    cP
    cfv
    @11
    c1
    caddc
    co
    #
    cP
    cfv
    cpr
    wceq
    vk
    cc0
    @8
    cfzo
    co
    wral
    #
    w3a
    #
    @5
    @4
    wi
    @0
    vf
    cv
    #
    @6
    wcel
    cc0
    @15
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
    @11
    @15
    cfv
    cI
    cfv
    @11
    @17
    cfv
    @12
    @17
    cfv
    cpr
    wceq
    vk
    cc0
    @16
    cfzo
    co
    wral
    w3a
    vf
    vp
    cF
    cP
    cupwlks
    cG
    vf
    vk
    cG
    cI
    cV
    cvv
    vp
    upwlksfval.v
    upwlksfval.i
    upwlksfval
    brfvopab
    a1i
    @0
    @14
    @1
    @2
    @3
    wa
    #
    wa
    #
    @4
    @0
    @14
    @19
    @0
    @1
    @14
    @18
    cG
    cW
    elex
    @7
    @10
    @18
    @13
    @7
    @2
    @10
    @3
    cF
    @6
    elex
    @10
    cP
    cV
    @9
    cpm
    co
    @9
    cV
    cP
    cc0
    @8
    cfz
    ovex
    cV
    cG
    cvtx
    upwlksfval.v
    fvexi
    fpm
    elexd
    anim12i
    3adant3
    anim12i
    ex
    @1
    @2
    @3
    3anass
    syl6ibr
    @4
    @5
    @14
    wb
    wi
    @0
    cP
    cvv
    vk
    cF
    cG
    cI
    cV
    cvv
    cvv
    upwlksfval.v
    upwlksfval.i
    isupwlk
    a1i
    pm5.21ndd
end
