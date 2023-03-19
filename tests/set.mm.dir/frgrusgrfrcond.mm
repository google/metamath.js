include "cfrgr.mm"
include "wcel.mm"
include "cusgr.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "wreu.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wa.mm"
include "isfrgr.mm"
include "simpl.mm"
include "syl6bi.mm"
include "pm2.43i.mm"
include "pm5.21nii.mm"

theorem frgrusgrfrcond
  let vx: setvar x
  let vk: setvar k
  let cE: class E
  let cG: class G
  let cV: class V
  let vl: setvar l
  let ve: setvar e
  let vh: setvar h
  let vg: setvar g
  let vv: setvar v
  assume isfrgr.v: |- V = ( Vtx ` G )
  assume isfrgr.e: |- E = ( Edg ` G )

  disjoint k l
  disjoint k x
  disjoint l x
  disjoint G k
  disjoint G l
  disjoint G x
  disjoint V k
  disjoint V l
  disjoint V x
  disjoint e h
  disjoint g h
  disjoint h k
  disjoint h l
  disjoint h x
  disjoint h v
  disjoint e g
  disjoint e k
  disjoint e l
  disjoint e x
  disjoint e v
  disjoint g k
  disjoint g l
  disjoint g x
  disjoint g v
  disjoint k v
  disjoint l v
  disjoint v x
  disjoint E h
  disjoint G h
  disjoint V h
  assert |- ( G e. FriendGraph <-> ( G e. USGraph /\ A. k e. V A. l e. ( V \ { k } ) E! x e. V { { x , k } , { x , l } } C_ E ) )

  proof
    cG
    cfrgr
    wcel
    #
    cG
    cusgr
    wcel
    #
    @1
    vx
    cv
    #
    vk
    cv
    #
    cpr
    @2
    vl
    cv
    cpr
    cpr
    cE
    wss
    vx
    cV
    wreu
    vl
    cV
    @3
    csn
    cdif
    wral
    vk
    cV
    wral
    #
    wa
    #
    @0
    @1
    @0
    @0
    @5
    @1
    vx
    cfrgr
    vk
    cE
    cG
    cV
    vl
    isfrgr.v
    isfrgr.e
    isfrgr
    @1
    @4
    simpl
    #
    syl6bi
    pm2.43i
    @6
    vx
    cusgr
    vk
    cE
    cG
    cV
    vl
    isfrgr.v
    isfrgr.e
    isfrgr
    pm5.21nii
end
