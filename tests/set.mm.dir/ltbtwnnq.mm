include "cltq.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "wex.mm"
include "cnq.mm"
include "wcel.mm"
include "ltrelnq.mm"
include "brel.mm"
include "simprd.mm"
include "cplq.mm"
include "co.mm"
include "wceq.mm"
include "ltexnq.mm"
include "eleq1.mm"
include "biimparc.mm"
include "cxp.mm"
include "addnqf.mm"
include "fdmi.mm"
include "0nnq.mm"
include "ndmovrcl.mm"
include "syl.mm"
include "nsmallnq.mm"
include "simpld.mm"
include "ltaddnq.mm"
include "syl2an.mm"
include "ltanq.mm"
include "biimpa.mm"
include "sylan.mm"
include "simplr.mm"
include "breqtrd.mm"
include "ovex.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "spcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5.mm"
include "mpd.mm"
include "sylbid.mm"
include "mpcom.mm"
include "ltsonq.mm"
include "sotri.mm"
include "exlimiv.mm"
include "impbii.mm"

theorem ltbtwnnq
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  assert |- ( A <Q B <-> E. x ( A <Q x /\ x <Q B ) )

  proof
    cA
    cB
    cltq
    wbr
    #
    cA
    vx
    cv
    #
    cltq
    wbr
    #
    @1
    cB
    cltq
    wbr
    #
    wa
    #
    vx
    wex
    #
    cB
    cnq
    wcel
    #
    @0
    @5
    @0
    cA
    cnq
    wcel
    #
    @6
    cA
    cB
    cnq
    cnq
    cltq
    ltrelnq
    brel
    simprd
    @6
    @0
    cA
    vy
    cv
    #
    cplq
    co
    #
    cB
    wceq
    #
    vy
    wex
    @5
    vy
    cA
    cB
    ltexnq
    @6
    @10
    @5
    vy
    @6
    @10
    @5
    @6
    @10
    wa
    #
    @8
    cnq
    wcel
    #
    @5
    @11
    @7
    @12
    @11
    @9
    cnq
    wcel
    #
    @7
    @12
    wa
    @10
    @13
    @6
    @9
    cB
    cnq
    eleq1
    biimparc
    cA
    @8
    cnq
    cplq
    cnq
    cnq
    cxp
    cnq
    cplq
    addnqf
    fdmi
    0nnq
    ndmovrcl
    syl
    #
    simprd
    @12
    vz
    cv
    #
    @8
    cltq
    wbr
    #
    vz
    wex
    @11
    @5
    vz
    @8
    nsmallnq
    @11
    @16
    @5
    vz
    @11
    @16
    @5
    @11
    @16
    wa
    #
    cA
    cA
    @15
    cplq
    co
    #
    cltq
    wbr
    #
    @18
    cB
    cltq
    wbr
    #
    @5
    @11
    @7
    @15
    cnq
    wcel
    #
    @19
    @16
    @11
    @7
    @12
    @14
    simpld
    #
    @16
    @21
    @12
    @15
    @8
    cnq
    cnq
    cltq
    ltrelnq
    brel
    simpld
    cA
    @15
    ltaddnq
    syl2an
    @17
    @18
    @9
    cB
    cltq
    @11
    @7
    @16
    @18
    @9
    cltq
    wbr
    #
    @22
    @7
    @16
    @23
    @15
    @8
    cA
    ltanq
    biimpa
    sylan
    @6
    @10
    @16
    simplr
    breqtrd
    @4
    @19
    @20
    wa
    vx
    @18
    cA
    @15
    cplq
    ovex
    @1
    @18
    wceq
    @2
    @19
    @3
    @20
    @1
    @18
    cA
    cltq
    breq2
    @1
    @18
    cB
    cltq
    breq1
    anbi12d
    spcev
    syl2anc
    ex
    exlimdv
    syl5
    mpd
    ex
    exlimdv
    sylbid
    mpcom
    @4
    @0
    vx
    cA
    @1
    cB
    cltq
    cnq
    ltsonq
    ltrelnq
    sotri
    exlimiv
    impbii
end
