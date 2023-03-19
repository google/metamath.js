include "cgrp.mm"
include "wcel.mm"
include "csn.mm"
include "cfv.mm"
include "cfn.mm"
include "w3a.mm"
include "chash.mm"
include "cn.mm"
include "wceq.mm"
include "cn0.mm"
include "cc0.mm"
include "wne.mm"
include "odcl.mm"
include "3ad2ant2.mm"
include "cr.mm"
include "wa.mm"
include "hashcl.mm"
include "nn0red.mm"
include "wn.mm"
include "cpnf.mm"
include "pnfnre.mm"
include "neli.mm"
include "odhash.mm"
include "eleq1d.mm"
include "mtbiri.mm"
include "3expia.mm"
include "necon2ad.mm"
include "syl5.mm"
include "3impia.mm"
include "elnnne0.mm"
include "sylanbrc.mm"
include "odhash2.mm"
include "syld3an3.mm"
include "eqcomd.mm"

theorem odhash3
  let cA: class A
  let cG: class G
  let cK: class K
  let cO: class O
  let cX: class X
  let vx: setvar x
  assume odhash.x: |- X = ( Base ` G )
  assume odhash.o: |- O = ( od ` G )
  assume odhash.k: |- K = ( mrCls ` ( SubGrp ` G ) )


  assert |- ( ( G e. Grp /\ A e. X /\ ( K ` { A } ) e. Fin ) -> ( O ` A ) = ( # ` ( K ` { A } ) ) )

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
    csn
    cK
    cfv
    #
    cfn
    wcel
    #
    w3a
    #
    @2
    chash
    cfv
    #
    cA
    cO
    cfv
    #
    @0
    @1
    @3
    @6
    cn
    wcel
    #
    @5
    @6
    wceq
    @4
    @6
    cn0
    wcel
    #
    @6
    cc0
    wne
    #
    @7
    @1
    @0
    @8
    @3
    cA
    cG
    cO
    cX
    odhash.x
    odhash.o
    odcl
    3ad2ant2
    @0
    @1
    @3
    @9
    @3
    @5
    cr
    wcel
    #
    @0
    @1
    wa
    #
    @9
    @3
    @5
    @2
    hashcl
    nn0red
    @11
    @10
    @6
    cc0
    @0
    @1
    @6
    cc0
    wceq
    #
    @10
    wn
    @0
    @1
    @12
    w3a
    #
    @10
    cpnf
    cr
    wcel
    cpnf
    cr
    pnfnre
    neli
    @13
    @5
    cpnf
    cr
    cA
    cG
    cK
    cO
    cX
    odhash.x
    odhash.o
    odhash.k
    odhash
    eleq1d
    mtbiri
    3expia
    necon2ad
    syl5
    3impia
    @6
    elnnne0
    sylanbrc
    cA
    cG
    cK
    cO
    cX
    odhash.x
    odhash.o
    odhash.k
    odhash2
    syld3an3
    eqcomd
end
