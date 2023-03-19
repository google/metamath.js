include "cgrp.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "wa.mm"
include "cfv.mm"
include "wne.mm"
include "eldifi.mm"
include "grpinvcl.mm"
include "sylan2.mm"
include "eldifsn.mm"
include "grpinvnz.mm"
include "3expb.mm"
include "sylan2b.mm"
include "sylanbrc.mm"

theorem grpinvnzcl
  let cB: class B
  let cG: class G
  let cN: class N
  let cX: class X
  let c.0: class .0.
  assume grpinvnzcl.b: |- B = ( Base ` G )
  assume grpinvnzcl.z: |- .0. = ( 0g ` G )
  assume grpinvnzcl.n: |- N = ( invg ` G )


  assert |- ( ( G e. Grp /\ X e. ( B \ { .0. } ) ) -> ( N ` X ) e. ( B \ { .0. } ) )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cB
    c.0
    csn
    #
    cdif
    #
    wcel
    #
    wa
    cX
    cN
    cfv
    #
    cB
    wcel
    #
    @4
    c.0
    wne
    #
    @4
    @2
    wcel
    @3
    @0
    cX
    cB
    wcel
    #
    @5
    cX
    cB
    @1
    eldifi
    cB
    cG
    cN
    cX
    grpinvnzcl.b
    grpinvnzcl.n
    grpinvcl
    sylan2
    @3
    @0
    @7
    cX
    c.0
    wne
    #
    wa
    @6
    cX
    cB
    c.0
    eldifsn
    @0
    @7
    @8
    @6
    cB
    cG
    cN
    cX
    c.0
    grpinvnzcl.b
    grpinvnzcl.z
    grpinvnzcl.n
    grpinvnz
    3expb
    sylan2b
    @4
    cB
    c.0
    eldifsn
    sylanbrc
end
