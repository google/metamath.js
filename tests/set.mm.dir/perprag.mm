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
include "ragtrivb.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "wne.mm"
include "co.mm"
include "cstrkg.mm"
include "crn.mm"
include "tglngne.mm"
include "tgelrnln.mm"
include "tglnpt.mm"
include "tglinerflx1.mm"
include "elind.mm"
include "tglinerflx2.mm"
include "cperpg.mm"
include "wbr.mm"
include "isperp2d.mm"
include "pm2.61dane.mm"

theorem perprag
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
  assume perprag.1: |- ( ph -> A e. P )
  assume perprag.2: |- ( ph -> B e. P )
  assume perprag.3: |- ( ph -> C e. ( A L B ) )
  assume perprag.4: |- ( ph -> D e. P )
  assume perprag.5: |- ( ph -> ( A L B ) ( perpG ` G ) ( C L D ) )


  assert |- ( ph -> <" A C D "> e. ( raG ` G ) )

  proof
    wph
    cA
    cC
    cD
    cs3
    #
    cG
    crag
    cfv
    #
    wcel
    cC
    cD
    wph
    cC
    cD
    wceq
    #
    wa
    #
    @0
    cA
    cD
    cD
    cs3
    #
    @1
    @3
    cA
    cC
    cD
    cD
    cA
    cD
    @3
    cA
    eqidd
    wph
    @2
    simpr
    @3
    cD
    eqidd
    s3eqd
    wph
    @4
    @1
    wcel
    @2
    wph
    cA
    cD
    cD
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
    colperpex.g
    perprag.1
    perprag.4
    perprag.4
    ragtrivb
    adantr
    eqeltrd
    wph
    cC
    cD
    wne
    #
    wa
    #
    cA
    cB
    cL
    co
    #
    cC
    cD
    cL
    co
    #
    cP
    cA
    cG
    cI
    cL
    c.mi
    cD
    cC
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    wph
    cG
    cstrkg
    wcel
    @6
    colperpex.g
    adantr
    #
    wph
    @8
    cL
    crn
    wcel
    @6
    wph
    cP
    cG
    cI
    cL
    cA
    cB
    colperpex.p
    colperpex.i
    colperpex.l
    colperpex.g
    perprag.1
    perprag.2
    wph
    cP
    cG
    cI
    cL
    cA
    cB
    cC
    colperpex.p
    colperpex.l
    colperpex.i
    colperpex.g
    perprag.1
    perprag.2
    perprag.3
    tglngne
    #
    tgelrnln
    #
    adantr
    @7
    cP
    cG
    cI
    cL
    cC
    cD
    colperpex.p
    colperpex.i
    colperpex.l
    @10
    wph
    cC
    cP
    wcel
    @6
    wph
    @8
    cP
    cG
    cI
    cL
    cC
    colperpex.p
    colperpex.l
    colperpex.i
    colperpex.g
    @12
    perprag.3
    tglnpt
    adantr
    #
    wph
    cD
    cP
    wcel
    @6
    perprag.4
    adantr
    #
    wph
    @6
    simpr
    #
    tgelrnln
    @7
    @8
    @9
    cC
    wph
    cC
    @8
    wcel
    @6
    perprag.3
    adantr
    @7
    cP
    cC
    cD
    cG
    cI
    cL
    colperpex.p
    colperpex.i
    colperpex.l
    @10
    @13
    @14
    @15
    tglinerflx1
    elind
    wph
    cA
    @8
    wcel
    @6
    wph
    cP
    cA
    cB
    cG
    cI
    cL
    colperpex.p
    colperpex.i
    colperpex.l
    colperpex.g
    perprag.1
    perprag.2
    @11
    tglinerflx1
    adantr
    @7
    cP
    cC
    cD
    cG
    cI
    cL
    colperpex.p
    colperpex.i
    colperpex.l
    @10
    @13
    @14
    @15
    tglinerflx2
    wph
    @8
    @9
    cG
    cperpg
    cfv
    wbr
    @6
    perprag.5
    adantr
    isperp2d
    pm2.61dane
end
