include "cgrp.mm"
include "wcel.mm"
include "cfv.mm"
include "cn.mm"
include "w3a.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "chash.mm"
include "csn.mm"
include "cv.mm"
include "cmg.mm"
include "cmpt.mm"
include "wf1o.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "eqid.mm"
include "odf1o2.mm"
include "ovex.mm"
include "f1oen.mm"
include "hasheni.mm"
include "3syl.mm"
include "cn0.mm"
include "odcl.mm"
include "3ad2ant2.mm"
include "hashfzo0.mm"
include "syl.mm"
include "eqtr3d.mm"

theorem odhash2
  let cA: class A
  let cG: class G
  let cK: class K
  let cO: class O
  let cX: class X
  let vx: setvar x
  assume odhash.x: |- X = ( Base ` G )
  assume odhash.o: |- O = ( od ` G )
  assume odhash.k: |- K = ( mrCls ` ( SubGrp ` G ) )


  assert |- ( ( G e. Grp /\ A e. X /\ ( O ` A ) e. NN ) -> ( # ` ( K ` { A } ) ) = ( O ` A ) )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    cA
    cO
    cfv
    #
    cn
    wcel
    #
    w3a
    #
    cc0
    @2
    cfzo
    co
    #
    chash
    cfv
    #
    cA
    csn
    cK
    cfv
    #
    chash
    cfv
    #
    @2
    @4
    @5
    @7
    vx
    @5
    vx
    cv
    cA
    cG
    cmg
    cfv
    #
    co
    cmpt
    #
    wf1o
    @5
    @7
    cen
    wbr
    @6
    @8
    wceq
    vx
    cA
    @9
    cG
    cK
    cO
    cX
    odhash.x
    @9
    eqid
    odhash.o
    odhash.k
    odf1o2
    @5
    @7
    @10
    cc0
    @2
    cfzo
    ovex
    f1oen
    @5
    @7
    hasheni
    3syl
    @4
    @2
    cn0
    wcel
    #
    @6
    @2
    wceq
    @1
    @0
    @11
    @3
    cA
    cG
    cO
    cX
    odhash.x
    odhash.o
    odcl
    3ad2ant2
    @2
    hashfzo0
    syl
    eqtr3d
end
