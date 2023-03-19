include "cdomn.mm"
include "wcel.mm"
include "cnzr.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "wss.mm"
include "eqid.mm"
include "isdomn.mm"
include "dfss3.mm"
include "wne.mm"
include "isrrg.mm"
include "baib.mm"
include "imbi2d.mm"
include "ralbiia.mm"
include "eldifsn.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bitri.mm"
include "ralbii2.mm"
include "wn.mm"
include "con34b.mm"
include "ioran.mm"
include "df-ne.mm"
include "imbi12i.mm"
include "3bitr4i.mm"
include "ralbii.mm"
include "r19.21v.mm"
include "bitr2i.mm"
include "anbi2i.mm"

theorem isdomn2
  let cB: class B
  let cR: class R
  let cE: class E
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume isdomn2.b: |- B = ( Base ` R )
  assume isdomn2.t: |- E = ( RLReg ` R )
  assume isdomn2.z: |- .0. = ( 0g ` R )


  assert |- ( R e. Domn <-> ( R e. NzRing /\ ( B \ { .0. } ) C_ E ) )

  proof
    cR
    cdomn
    wcel
    cR
    cnzr
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    cmulr
    cfv
    #
    co
    c.0
    wceq
    #
    @1
    c.0
    wceq
    #
    @2
    c.0
    wceq
    #
    wo
    #
    wi
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    wa
    @0
    cB
    c.0
    csn
    cdif
    #
    cE
    wss
    #
    wa
    vx
    vy
    cB
    cR
    @3
    c.0
    isdomn2.b
    @3
    eqid
    #
    isdomn2.z
    isdomn
    @10
    @12
    @0
    @12
    @1
    cE
    wcel
    #
    vx
    @11
    wral
    #
    @10
    vx
    @11
    cE
    dfss3
    @1
    c.0
    wne
    #
    @14
    wi
    #
    vx
    cB
    wral
    @16
    @4
    @6
    wi
    #
    vy
    cB
    wral
    #
    wi
    #
    vx
    cB
    wral
    @15
    @10
    @17
    @20
    vx
    cB
    @1
    cB
    wcel
    #
    @14
    @19
    @16
    @14
    @21
    @19
    vy
    cB
    cR
    @3
    cE
    @1
    c.0
    isdomn2.t
    isdomn2.b
    @13
    isdomn2.z
    isrrg
    baib
    imbi2d
    ralbiia
    @14
    @17
    vx
    @11
    cB
    @1
    @11
    wcel
    #
    @14
    wi
    @21
    @16
    wa
    #
    @14
    wi
    @21
    @17
    wi
    @22
    @23
    @14
    @1
    cB
    c.0
    eldifsn
    imbi1i
    @21
    @16
    @14
    impexp
    bitri
    ralbii2
    @9
    @20
    vx
    cB
    @9
    @16
    @18
    wi
    #
    vy
    cB
    wral
    @20
    @8
    @24
    vy
    cB
    @8
    @7
    wn
    #
    @4
    wn
    #
    wi
    #
    @24
    @4
    @7
    con34b
    @5
    wn
    #
    @6
    wn
    #
    wa
    #
    @26
    wi
    @28
    @29
    @26
    wi
    #
    wi
    @27
    @24
    @28
    @29
    @26
    impexp
    @25
    @30
    @26
    @5
    @6
    ioran
    imbi1i
    @16
    @28
    @18
    @31
    @1
    c.0
    df-ne
    @4
    @6
    con34b
    imbi12i
    3bitr4i
    bitri
    ralbii
    @16
    @18
    vy
    cB
    r19.21v
    bitri
    ralbii
    3bitr4i
    bitr2i
    anbi2i
    bitri
end
