include "cs3.mm"
include "crag.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "eqidd.mm"
include "simpr.mm"
include "s3eqd.mm"
include "cmir.mm"
include "eqid.mm"
include "co.mm"
include "perpln1.mm"
include "tglnpt.mm"
include "ragtrivb.mm"
include "ragcom.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "wne.mm"
include "cstrkg.mm"
include "crn.mm"
include "tglinethru.mm"
include "eleqtrd.mm"
include "cperpg.mm"
include "wbr.mm"
include "eqbrtrrd.mm"
include "perprag.mm"
include "pm2.61dane.mm"

theorem perpdragALT
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  assume colperpex.p: |- P = ( Base ` G )
  assume colperpex.d: |- .- = ( dist ` G )
  assume colperpex.i: |- I = ( Itv ` G )
  assume colperpex.l: |- L = ( LineG ` G )
  assume colperpex.g: |- ( ph -> G e. TarskiG )
  assume perpdrag.1: |- ( ph -> A e. D )
  assume perpdrag.2: |- ( ph -> B e. D )
  assume perpdrag.3: |- ( ph -> C e. P )
  assume perpdrag.4: |- ( ph -> D ( perpG ` G ) ( B L C ) )


  assert |- ( ph -> <" A B C "> e. ( raG ` G ) )

  proof
    wph
    cA
    cB
    cC
    cs3
    #
    cG
    crag
    cfv
    #
    wcel
    cA
    cB
    wph
    cA
    cB
    wceq
    #
    wa
    #
    cA
    cA
    cC
    cs3
    #
    @0
    @1
    @3
    cA
    cA
    cC
    cC
    cA
    cB
    @3
    cA
    eqidd
    wph
    @2
    simpr
    @3
    cC
    eqidd
    s3eqd
    wph
    @4
    @1
    wcel
    @2
    wph
    cC
    cA
    cA
    cP
    cG
    cmir
    cfv
    #
    cG
    cI
    cL
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    @5
    eqid
    #
    colperpex.g
    perpdrag.3
    wph
    cD
    cP
    cG
    cI
    cL
    cA
    colperpex.p
    colperpex.l
    colperpex.i
    colperpex.g
    wph
    cD
    cB
    cC
    cL
    co
    #
    cG
    cL
    colperpex.l
    colperpex.g
    perpdrag.4
    perpln1
    #
    perpdrag.1
    tglnpt
    #
    @9
    wph
    cC
    cA
    cC
    cP
    @5
    cG
    cI
    cL
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    @6
    colperpex.g
    perpdrag.3
    @9
    perpdrag.3
    ragtrivb
    ragcom
    adantr
    eqeltrrd
    wph
    cA
    cB
    wne
    #
    wa
    #
    cA
    cB
    cB
    cC
    cP
    cG
    cI
    cL
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    wph
    cG
    cstrkg
    wcel
    @10
    colperpex.g
    adantr
    #
    wph
    cA
    cP
    wcel
    @10
    @9
    adantr
    #
    wph
    cB
    cP
    wcel
    @10
    wph
    cD
    cP
    cG
    cI
    cL
    cB
    colperpex.p
    colperpex.l
    colperpex.i
    colperpex.g
    @8
    perpdrag.2
    tglnpt
    adantr
    #
    @11
    cB
    cD
    cA
    cB
    cL
    co
    #
    wph
    cB
    cD
    wcel
    @10
    perpdrag.2
    adantr
    #
    @11
    cD
    cP
    cA
    cB
    cG
    cI
    cL
    colperpex.p
    colperpex.i
    colperpex.l
    @12
    @13
    @14
    wph
    @10
    simpr
    #
    @17
    wph
    cD
    cL
    crn
    wcel
    @10
    @8
    adantr
    wph
    cA
    cD
    wcel
    @10
    perpdrag.1
    adantr
    @16
    tglinethru
    #
    eleqtrd
    wph
    cC
    cP
    wcel
    @10
    perpdrag.3
    adantr
    @11
    cD
    @15
    @7
    cG
    cperpg
    cfv
    #
    @18
    wph
    cD
    @7
    @19
    wbr
    @10
    perpdrag.4
    adantr
    eqbrtrrd
    perprag
    pm2.61dane
end
