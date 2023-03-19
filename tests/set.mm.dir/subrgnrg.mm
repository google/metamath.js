include "cnrg.mm"
include "wcel.mm"
include "csubrg.mm"
include "cfv.mm"
include "wa.mm"
include "cngp.mm"
include "cnm.mm"
include "cabv.mm"
include "csubg.mm"
include "nrgngp.mm"
include "subrgsubg.mm"
include "subgngp.mm"
include "syl2an.mm"
include "cres.mm"
include "wceq.mm"
include "adantl.mm"
include "eqid.mm"
include "subgnm.mm"
include "syl.mm"
include "nrgabv.mm"
include "abvres.mm"
include "sylan.mm"
include "eqeltrd.mm"
include "isnrg.mm"
include "sylanbrc.mm"

theorem subrgnrg
  let cA: class A
  let cG: class G
  let cH: class H
  assume subrgnrg.h: |- H = ( G |`s A )


  assert |- ( ( G e. NrmRing /\ A e. ( SubRing ` G ) ) -> H e. NrmRing )

  proof
    cG
    cnrg
    wcel
    #
    cA
    cG
    csubrg
    cfv
    wcel
    #
    wa
    #
    cH
    cngp
    wcel
    #
    cH
    cnm
    cfv
    #
    cH
    cabv
    cfv
    #
    wcel
    cH
    cnrg
    wcel
    @0
    cG
    cngp
    wcel
    cA
    cG
    csubg
    cfv
    wcel
    #
    @3
    @1
    cG
    nrgngp
    cA
    cG
    subrgsubg
    #
    cA
    cG
    cH
    subrgnrg.h
    subgngp
    syl2an
    @2
    @4
    cG
    cnm
    cfv
    #
    cA
    cres
    #
    @5
    @2
    @6
    @4
    @9
    wceq
    @1
    @6
    @0
    @7
    adantl
    cA
    cG
    cH
    @4
    @8
    subrgnrg.h
    @8
    eqid
    #
    @4
    eqid
    #
    subgnm
    syl
    @0
    @8
    cG
    cabv
    cfv
    #
    wcel
    @1
    @9
    @5
    wcel
    @12
    cG
    @8
    @10
    @12
    eqid
    #
    nrgabv
    @12
    @5
    cA
    cG
    cH
    @8
    @13
    subrgnrg.h
    @5
    eqid
    #
    abvres
    sylan
    eqeltrd
    @5
    cH
    @4
    @11
    @14
    isnrg
    sylanbrc
end
