include "wcel.mm"
include "com.mm"
include "cwdom.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "csuc.mm"
include "cfv.mm"
include "wss.mm"
include "wral.mm"
include "crn.mm"
include "cint.mm"
include "wi.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "elmapi.mm"
include "wa.mm"
include "w3a.mm"
include "isf32lem11.mm"
include "expcom.mm"
include "3expa.mm"
include "impancom.mm"
include "con1d.mm"
include "exp31.mm"
include "syl.mm"
include "com4t.mm"
include "ralrimdv.mm"
include "isfin3ds.mm"
include "sylibrd.mm"

theorem isf32lem12
  let vx: setvar x
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vh: setvar h
  let vk: setvar k
  let vl: setvar l
  assume isf32lem40.f: |- F = { g | A. a e. ( ~P g ^m _om ) ( A. x e. _om ( a ` suc x ) C_ ( a ` x ) -> |^| ran a e. ran a ) }

  disjoint F g
  disjoint a g
  disjoint a x
  disjoint G a
  disjoint g x
  disjoint G g
  disjoint G x
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b k
  disjoint b l
  disjoint F b
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c k
  disjoint c l
  disjoint F c
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d h
  disjoint d k
  disjoint d l
  disjoint F d
  disjoint e f
  disjoint e g
  disjoint e h
  disjoint e k
  disjoint e l
  disjoint F e
  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f l
  disjoint F f
  disjoint g h
  disjoint g k
  disjoint g l
  disjoint h k
  disjoint h l
  disjoint F h
  disjoint k l
  disjoint F k
  disjoint F l
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a h
  disjoint a k
  disjoint a l
  disjoint b x
  disjoint G b
  disjoint c x
  disjoint G c
  disjoint d x
  disjoint G d
  disjoint f x
  disjoint G f
  disjoint h x
  disjoint G h
  disjoint k x
  disjoint G k
  disjoint l x
  disjoint G l
  disjoint V f
  assert |- ( G e. V -> ( -. _om ~<_* G -> G e. F ) )

  proof
    cG
    cV
    wcel
    #
    com
    cG
    cwdom
    wbr
    #
    wn
    #
    vb
    cv
    #
    csuc
    vf
    cv
    #
    cfv
    @3
    @4
    cfv
    wss
    vb
    com
    wral
    #
    @4
    crn
    #
    cint
    @6
    wcel
    #
    wi
    #
    vf
    cG
    cpw
    #
    com
    cmap
    co
    #
    wral
    cG
    cF
    wcel
    @0
    @2
    @8
    vf
    @10
    @4
    @10
    wcel
    #
    @5
    @0
    @2
    @7
    @11
    com
    @9
    @4
    wf
    #
    @5
    @0
    @2
    @7
    wi
    #
    wi
    wi
    @4
    @9
    com
    elmapi
    @12
    @5
    @0
    @13
    @12
    @5
    wa
    #
    @0
    wa
    @7
    @1
    @14
    @7
    wn
    #
    @0
    @1
    @12
    @5
    @15
    @0
    @1
    wi
    @0
    @12
    @5
    @15
    w3a
    @1
    @4
    cG
    cV
    vb
    isf32lem11
    expcom
    3expa
    impancom
    con1d
    exp31
    syl
    com4t
    ralrimdv
    vb
    cG
    vf
    vg
    cF
    cV
    va
    vx
    isf32lem40.f
    isfin3ds
    sylibrd
end
