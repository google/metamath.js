include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "cmpt.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "simpl.mm"
include "ssrab2.mm"
include "a1i.mm"
include "mre1cl.mm"
include "adantr.mm"
include "elpwi.mm"
include "adantl.mm"
include "sseq2.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "syl.mm"
include "mreintcl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "fmptd.mm"

theorem mrcflem
  let vx: setvar x
  let cC: class C
  let cX: class X
  let vs: setvar s
  let cF: class F
  let vc: setvar c
  let cU: class U
  let cV: class V

  disjoint s x
  disjoint C x
  disjoint C s
  disjoint X x
  disjoint X s
  disjoint F c
  disjoint F x
  disjoint F s
  disjoint c x
  disjoint c s
  disjoint C c
  disjoint X c
  disjoint U c
  disjoint U x
  disjoint U s
  disjoint V c
  disjoint V x
  disjoint V s
  assert |- ( C e. ( Moore ` X ) -> ( x e. ~P X |-> |^| { s e. C | x C_ s } ) : ~P X --> C )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    #
    vx
    cX
    cpw
    #
    vx
    cv
    #
    vs
    cv
    #
    wss
    #
    vs
    cC
    crab
    #
    cint
    #
    cC
    vx
    @1
    @6
    cmpt
    #
    @0
    @2
    @1
    wcel
    #
    wa
    #
    @0
    @5
    cC
    wss
    #
    @5
    c0
    wne
    #
    @6
    cC
    wcel
    @0
    @8
    simpl
    @10
    @9
    @4
    vs
    cC
    ssrab2
    a1i
    @9
    cX
    @5
    wcel
    #
    @11
    @9
    cX
    cC
    wcel
    #
    @2
    cX
    wss
    #
    @12
    @0
    @13
    @8
    cC
    cX
    mre1cl
    adantr
    @8
    @14
    @0
    @2
    cX
    elpwi
    adantl
    @4
    @14
    vs
    cX
    cC
    @3
    cX
    @2
    sseq2
    elrab
    sylanbrc
    @5
    cX
    ne0i
    syl
    cC
    @5
    cX
    mreintcl
    syl3anc
    @7
    eqid
    fmptd
end
