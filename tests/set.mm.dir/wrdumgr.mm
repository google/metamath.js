include "wcel.mm"
include "cword.mm"
include "wa.mm"
include "cumgr.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "wf.mm"
include "wb.mm"
include "isumgrs.mm"
include "adantr.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wrdf.mm"
include "adantl.mm"
include "fdm.mm"
include "syl.mm"
include "feq2d.mm"
include "iswrdi.mm"
include "impbii.mm"
include "syl6bb.mm"
include "bitrd.mm"

theorem wrdumgr
  let vx: setvar x
  let cU: class U
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let ve: setvar e
  let vg: setvar g
  let vh: setvar h
  let vv: setvar v
  assume isumgr.v: |- V = ( Vtx ` G )
  assume isumgr.e: |- E = ( iEdg ` G )

  disjoint G x
  disjoint V x
  disjoint e g
  disjoint e h
  disjoint e v
  disjoint e x
  disjoint g h
  disjoint g v
  disjoint g x
  disjoint h v
  disjoint h x
  disjoint v x
  disjoint E h
  disjoint G h
  disjoint V h
  assert |- ( ( G e. U /\ E e. Word X ) -> ( G e. UMGraph <-> E e. Word { x e. ~P V | ( # ` x ) = 2 } ) )

  proof
    cG
    cU
    wcel
    #
    cE
    cX
    cword
    wcel
    #
    wa
    #
    cG
    cumgr
    wcel
    #
    cE
    cdm
    #
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
    #
    cE
    wf
    #
    cE
    @5
    cword
    wcel
    #
    @0
    @3
    @6
    wb
    @1
    vx
    cU
    cE
    cG
    cV
    isumgr.v
    isumgr.e
    isumgrs
    adantr
    @2
    @6
    cc0
    cE
    chash
    cfv
    #
    cfzo
    co
    #
    @5
    cE
    wf
    #
    @7
    @2
    @4
    @9
    @5
    cE
    @2
    @9
    cX
    cE
    wf
    #
    @4
    @9
    wceq
    @1
    @11
    @0
    cX
    cE
    wrdf
    adantl
    @9
    cX
    cE
    fdm
    syl
    feq2d
    @10
    @7
    @5
    @8
    cE
    iswrdi
    @5
    cE
    wrdf
    impbii
    syl6bb
    bitrd
end
