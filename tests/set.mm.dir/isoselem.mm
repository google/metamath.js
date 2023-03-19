include "wse.mm"
include "ccnv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "cfv.mm"
include "wa.mm"
include "wi.mm"
include "dfse2.mm"
include "biimpi.mm"
include "r19.21bi.mm"
include "expcom.mm"
include "adantl.mm"
include "wceq.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "vtoclg.mm"
include "com12.mm"
include "adantr.mm"
include "wiso.mm"
include "isoini.mm"
include "sylan.mm"
include "sylibd.mm"
include "syld.mm"
include "ralrimdva.mm"
include "crn.mm"
include "wf1o.mm"
include "wfn.mm"
include "wb.mm"
include "isof1o.mm"
include "f1ofn.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "ineq2d.mm"
include "ralrn.mm"
include "4syl.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "raleqdv.mm"
include "bitr3d.mm"
include "syl6ibr.mm"

theorem isoselem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume isofrlem.1: |- ( ph -> H Isom R , S ( A , B ) )
  assume isofrlem.2: |- ( ph -> ( H " x ) e. _V )

  disjoint A x
  disjoint B x
  disjoint H x
  disjoint ph x
  disjoint R x
  disjoint S x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint H w
  disjoint H y
  disjoint H z
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint R w
  disjoint R y
  disjoint R z
  disjoint S w
  disjoint S y
  disjoint S z
  assert |- ( ph -> ( R Se A -> S Se B ) )

  proof
    wph
    cA
    cR
    wse
    #
    cB
    cS
    ccnv
    #
    vy
    cv
    #
    csn
    #
    cima
    #
    cin
    #
    cvv
    wcel
    #
    vy
    cB
    wral
    #
    cB
    cS
    wse
    wph
    @0
    cB
    @1
    vz
    cv
    #
    cH
    cfv
    #
    csn
    #
    cima
    #
    cin
    #
    cvv
    wcel
    #
    vz
    cA
    wral
    #
    @7
    wph
    @0
    @13
    vz
    cA
    wph
    @8
    cA
    wcel
    #
    wa
    #
    @0
    cA
    cR
    ccnv
    @8
    csn
    cima
    cin
    #
    cvv
    wcel
    #
    @13
    @15
    @0
    @18
    wi
    wph
    @0
    @15
    @18
    @0
    @18
    vz
    cA
    @0
    @18
    vz
    cA
    wral
    vz
    cA
    cR
    dfse2
    biimpi
    r19.21bi
    expcom
    adantl
    @16
    @18
    cH
    @17
    cima
    #
    cvv
    wcel
    #
    @13
    wph
    @18
    @20
    wi
    @15
    @18
    wph
    @20
    wph
    cH
    vx
    cv
    #
    cima
    #
    cvv
    wcel
    #
    wi
    wph
    @20
    wi
    vx
    @17
    cvv
    @21
    @17
    wceq
    #
    @23
    @20
    wph
    @24
    @22
    @19
    cvv
    @21
    @17
    cH
    imaeq2
    eleq1d
    imbi2d
    isofrlem.2
    vtoclg
    com12
    adantr
    @16
    @19
    @12
    cvv
    wph
    cA
    cB
    cR
    cS
    cH
    wiso
    #
    @15
    @19
    @12
    wceq
    isofrlem.1
    cA
    cB
    @8
    cR
    cS
    cH
    isoini
    sylan
    eleq1d
    sylibd
    syld
    ralrimdva
    wph
    @6
    vy
    cH
    crn
    #
    wral
    #
    @14
    @7
    wph
    @25
    cA
    cB
    cH
    wf1o
    #
    cH
    cA
    wfn
    @27
    @14
    wb
    isofrlem.1
    cA
    cB
    cR
    cS
    cH
    isof1o
    #
    cA
    cB
    cH
    f1ofn
    @6
    @13
    vy
    vz
    cA
    cH
    @2
    @9
    wceq
    #
    @5
    @12
    cvv
    @30
    @4
    @11
    cB
    @30
    @3
    @10
    @1
    @2
    @9
    sneq
    imaeq2d
    ineq2d
    eleq1d
    ralrn
    4syl
    wph
    @6
    vy
    @26
    cB
    wph
    @25
    @28
    cA
    cB
    cH
    wfo
    @26
    cB
    wceq
    isofrlem.1
    @29
    cA
    cB
    cH
    f1ofo
    cA
    cB
    cH
    forn
    4syl
    raleqdv
    bitr3d
    sylibd
    vy
    cB
    cS
    dfse2
    syl6ibr
end
