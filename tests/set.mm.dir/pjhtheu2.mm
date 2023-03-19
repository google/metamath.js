include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "cv.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "cort.mm"
include "cfv.mm"
include "wrex.mm"
include "wreu.mm"
include "choccl.mm"
include "pjhtheu.mm"
include "sylan.mm"
include "simpll.mm"
include "ococ.mm"
include "syl.mm"
include "rexeqdv.mm"
include "adantr.mm"
include "chel.mm"
include "ax-hvcom.mm"
include "syl2anc.mm"
include "eqeq2d.mm"
include "rexbidva.mm"
include "bitrd.mm"
include "reubidva.mm"
include "mpbid.mm"

theorem pjhtheu2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cH: class H

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint H x
  disjoint H y
  assert |- ( ( H e. CH /\ A e. ~H ) -> E! y e. ( _|_ ` H ) E. x e. H A = ( x +h y ) )

  proof
    cH
    cch
    wcel
    #
    cA
    chil
    wcel
    #
    wa
    #
    cA
    vy
    cv
    #
    vx
    cv
    #
    cva
    co
    #
    wceq
    #
    vx
    cH
    cort
    cfv
    #
    cort
    cfv
    #
    wrex
    #
    vy
    @7
    wreu
    #
    cA
    @4
    @3
    cva
    co
    #
    wceq
    #
    vx
    cH
    wrex
    #
    vy
    @7
    wreu
    @0
    @7
    cch
    wcel
    #
    @1
    @10
    cH
    choccl
    #
    vy
    vx
    cA
    @7
    pjhtheu
    sylan
    @2
    @9
    @13
    vy
    @7
    @2
    @3
    @7
    wcel
    #
    wa
    #
    @9
    @6
    vx
    cH
    wrex
    @13
    @17
    @6
    vx
    @8
    cH
    @17
    @0
    @8
    cH
    wceq
    @0
    @1
    @16
    simpll
    #
    cH
    ococ
    syl
    rexeqdv
    @17
    @6
    @12
    vx
    cH
    @17
    @4
    cH
    wcel
    #
    wa
    #
    @5
    @11
    cA
    @20
    @3
    chil
    wcel
    #
    @4
    chil
    wcel
    #
    @5
    @11
    wceq
    @17
    @21
    @19
    @2
    @14
    @16
    @21
    @0
    @14
    @1
    @15
    adantr
    @3
    @7
    chel
    sylan
    adantr
    @17
    @0
    @19
    @22
    @18
    @4
    cH
    chel
    sylan
    @3
    @4
    ax-hvcom
    syl2anc
    eqeq2d
    rexbidva
    bitrd
    reubidva
    mpbid
end
