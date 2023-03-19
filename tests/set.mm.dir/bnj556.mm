include "cv.mm"
include "wcel.mm"
include "csuc.mm"
include "wceq.mm"
include "w3a.mm"
include "com.mm"
include "wa.mm"
include "vex.mm"
include "bnj216.mm"
include "3anim3i.mm"
include "adantr.mm"
include "w-bnj17.mm"
include "bnj258.mm"
include "bitri.mm"
include "3imtr4i.mm"

theorem bnj556
  let wet: wff et
  let wsi: wff si
  let cD: class D
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  assume bnj556.18: |- ( si <-> ( m e. D /\ n = suc m /\ p e. m ) )
  assume bnj556.19: |- ( et <-> ( m e. D /\ n = suc m /\ p e. _om /\ m = suc p ) )


  assert |- ( et -> si )

  proof
    vm
    cv
    #
    cD
    wcel
    #
    vn
    cv
    @0
    csuc
    wceq
    #
    @0
    vp
    cv
    #
    csuc
    wceq
    #
    w3a
    #
    @3
    com
    wcel
    #
    wa
    #
    @1
    @2
    @3
    @0
    wcel
    #
    w3a
    #
    wet
    wsi
    @5
    @9
    @6
    @4
    @8
    @1
    @2
    @0
    @3
    vp
    vex
    bnj216
    3anim3i
    adantr
    wet
    @1
    @2
    @6
    @4
    w-bnj17
    @7
    bnj556.19
    @1
    @2
    @6
    @4
    bnj258
    bitri
    bnj556.18
    3imtr4i
end
