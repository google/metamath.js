include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "wf1.mm"
include "wss.mm"
include "w3a.mm"
include "cid.mm"
include "cres.mm"
include "clindf.mm"
include "wbr.mm"
include "wa.mm"
include "ccom.mm"
include "clinds.mm"
include "cfv.mm"
include "cima.mm"
include "wb.mm"
include "ibar.mm"
include "3ad2ant3.mm"
include "wf.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "ax-mp.mm"
include "simp3.mm"
include "fss.mm"
include "sylancr.mm"
include "lindfmm.mm"
include "syld3an3.mm"
include "bitr3d.mm"
include "clmod.mm"
include "lmhmlmod1.mm"
include "3ad2ant1.mm"
include "islinds.mm"
include "syl.mm"
include "lmhmlmod2.mm"
include "adantr.mm"
include "simpr.mm"
include "f1ores.mm"
include "f1of1.mm"
include "3adant1.mm"
include "f1linds.mm"
include "syl3anc.mm"
include "crn.mm"
include "df-ima.mm"
include "lindfrn.mm"
include "sylan.mm"
include "syl5eqel.mm"
include "impbida.mm"
include "coires1.mm"
include "breq1i.mm"
include "syl6bbr.mm"
include "3bitr4d.mm"

theorem lindsmm
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vx: setvar x
  let cI: class I
  assume lindfmm.b: |- B = ( Base ` S )
  assume lindfmm.c: |- C = ( Base ` T )


  assert |- ( ( G e. ( S LMHom T ) /\ G : B -1-1-> C /\ F C_ B ) -> ( F e. ( LIndS ` S ) <-> ( G " F ) e. ( LIndS ` T ) ) )

  proof
    cG
    cS
    cT
    clmhm
    co
    wcel
    #
    cB
    cC
    cG
    wf1
    #
    cF
    cB
    wss
    #
    w3a
    #
    @2
    cid
    cF
    cres
    #
    cS
    clindf
    wbr
    #
    wa
    #
    cG
    @4
    ccom
    #
    cT
    clindf
    wbr
    #
    cF
    cS
    clinds
    cfv
    wcel
    #
    cG
    cF
    cima
    #
    cT
    clinds
    cfv
    #
    wcel
    #
    @3
    @5
    @6
    @8
    @2
    @0
    @5
    @6
    wb
    @1
    @2
    @5
    ibar
    3ad2ant3
    @0
    @1
    @2
    cF
    cB
    @4
    wf
    #
    @5
    @8
    wb
    @3
    cF
    cF
    @4
    wf
    #
    @2
    @13
    cF
    cF
    @4
    wf1o
    @14
    cF
    f1oi
    cF
    cF
    @4
    f1of
    ax-mp
    @0
    @1
    @2
    simp3
    cF
    cF
    cB
    @4
    fss
    sylancr
    cB
    cC
    cS
    cT
    @4
    cG
    cF
    lindfmm.b
    lindfmm.c
    lindfmm
    syld3an3
    bitr3d
    @3
    cS
    clmod
    wcel
    #
    @9
    @6
    wb
    @0
    @1
    @15
    @2
    cS
    cT
    cG
    lmhmlmod1
    3ad2ant1
    cB
    clmod
    cS
    cF
    lindfmm.b
    islinds
    syl
    @3
    @12
    cG
    cF
    cres
    #
    cT
    clindf
    wbr
    #
    @8
    @3
    @12
    @17
    @3
    @12
    wa
    cT
    clmod
    wcel
    #
    @12
    cF
    @10
    @16
    wf1
    #
    @17
    @3
    @18
    @12
    @0
    @1
    @18
    @2
    cS
    cT
    cG
    lmhmlmod2
    3ad2ant1
    #
    adantr
    @3
    @12
    simpr
    @3
    @19
    @12
    @1
    @2
    @19
    @0
    @1
    @2
    wa
    cF
    @10
    @16
    wf1o
    @19
    cB
    cC
    cF
    cG
    f1ores
    cF
    @10
    @16
    f1of1
    syl
    3adant1
    adantr
    cF
    @10
    @16
    cT
    f1linds
    syl3anc
    @3
    @17
    wa
    @10
    @16
    crn
    #
    @11
    cG
    cF
    df-ima
    @3
    @18
    @17
    @21
    @11
    wcel
    @20
    @16
    cT
    lindfrn
    sylan
    syl5eqel
    impbida
    @7
    @16
    cT
    clindf
    cG
    cF
    coires1
    breq1i
    syl6bbr
    3bitr4d
end
