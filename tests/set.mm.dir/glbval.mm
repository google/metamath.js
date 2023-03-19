include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "crio.mm"
include "wceq.mm"
include "wa.mm"
include "cpw.mm"
include "cv.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "cmpt.mm"
include "wreu.mm"
include "cab.mm"
include "cres.mm"
include "biid.mm"
include "adantr.mm"
include "glbfval.mm"
include "fveq1d.mm"
include "simpr.mm"
include "glbeu.mm"
include "wb.mm"
include "raleq.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "syl6bbr.mm"
include "reubidv.mm"
include "elabg.mm"
include "adantl.mm"
include "mpbird.mm"
include "fvres.mm"
include "syl.mm"
include "wss.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "sylibr.mm"
include "riotabidv.mm"
include "eqid.mm"
include "riotaex.mm"
include "fvmpt.mm"
include "3eqtrd.mm"
include "wn.mm"
include "c0.mm"
include "ndmfv.mm"
include "glbeldm.mm"
include "biimprd.mm"
include "mpand.mm"
include "con3dimp.mm"
include "riotaund.mm"
include "eqtr4d.mm"
include "pm2.61dan.mm"

theorem glbval
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cS: class S
  let cG: class G
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let vs: setvar s
  assume glbval.b: |- B = ( Base ` K )
  assume glbval.l: |- .<_ = ( le ` K )
  assume glbval.g: |- G = ( glb ` K )
  assume glbval.p: |- ( ps <-> ( A. y e. S x .<_ y /\ A. z e. B ( A. y e. S z .<_ y -> z .<_ x ) ) )
  assume glbva.k: |- ( ph -> K e. V )
  assume glbval.ss: |- ( ph -> S C_ B )

  disjoint x z
  disjoint B x
  disjoint B z
  disjoint x y
  disjoint K x
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint s x
  disjoint s z
  disjoint B s
  disjoint s y
  disjoint K s
  disjoint S s
  disjoint ps s
  assert |- ( ph -> ( G ` S ) = ( iota_ x e. B ps ) )

  proof
    wph
    cS
    cG
    cdm
    #
    wcel
    #
    cS
    cG
    cfv
    #
    wps
    vx
    cB
    crio
    #
    wceq
    wph
    @1
    wa
    #
    @2
    cS
    vs
    cB
    cpw
    #
    vx
    cv
    #
    vy
    cv
    #
    c.le
    wbr
    #
    vy
    vs
    cv
    #
    wral
    #
    vz
    cv
    #
    @7
    c.le
    wbr
    #
    vy
    @9
    wral
    #
    @11
    @6
    c.le
    wbr
    #
    wi
    #
    vz
    cB
    wral
    #
    wa
    #
    vx
    cB
    crio
    #
    cmpt
    #
    @17
    vx
    cB
    wreu
    #
    vs
    cab
    #
    cres
    #
    cfv
    #
    cS
    @19
    cfv
    #
    @3
    @4
    cS
    cG
    @22
    @4
    @17
    vx
    vy
    vz
    cB
    cG
    cK
    c.le
    cV
    vs
    glbval.b
    glbval.l
    glbval.g
    @17
    biid
    wph
    cK
    cV
    wcel
    @1
    glbva.k
    adantr
    #
    glbfval
    fveq1d
    @4
    cS
    @21
    wcel
    #
    @23
    @24
    wceq
    @4
    @26
    wps
    vx
    cB
    wreu
    #
    @4
    wps
    vx
    vy
    vz
    cB
    cS
    cG
    cK
    c.le
    cV
    glbval.b
    glbval.l
    glbval.g
    glbval.p
    @25
    wph
    @1
    simpr
    glbeu
    @1
    @26
    @27
    wb
    wph
    @20
    @27
    vs
    cS
    @0
    @9
    cS
    wceq
    #
    @17
    wps
    vx
    cB
    @28
    @17
    @8
    vy
    cS
    wral
    #
    @12
    vy
    cS
    wral
    #
    @14
    wi
    #
    vz
    cB
    wral
    #
    wa
    wps
    @28
    @10
    @29
    @16
    @32
    @8
    vy
    @9
    cS
    raleq
    @28
    @15
    @31
    vz
    cB
    @28
    @13
    @30
    @14
    @12
    vy
    @9
    cS
    raleq
    imbi1d
    ralbidv
    anbi12d
    glbval.p
    syl6bbr
    #
    reubidv
    elabg
    adantl
    mpbird
    cS
    @21
    @19
    fvres
    syl
    @4
    cS
    @5
    wcel
    #
    @24
    @3
    wceq
    @4
    cS
    cB
    wss
    #
    @34
    wph
    @35
    @1
    glbval.ss
    adantr
    cS
    cB
    cB
    cK
    cbs
    cfv
    cvv
    glbval.b
    cK
    cbs
    fvex
    eqeltri
    elpw2
    sylibr
    vs
    cS
    @18
    @3
    @5
    @19
    @28
    @17
    wps
    vx
    cB
    @33
    riotabidv
    @19
    eqid
    wps
    vx
    cB
    riotaex
    fvmpt
    syl
    3eqtrd
    wph
    @1
    wn
    #
    wa
    #
    @2
    c0
    @3
    @36
    @2
    c0
    wceq
    wph
    cS
    cG
    ndmfv
    adantl
    @37
    @27
    wn
    @3
    c0
    wceq
    wph
    @27
    @1
    wph
    @35
    @27
    @1
    glbval.ss
    wph
    @1
    @35
    @27
    wa
    wph
    wps
    vx
    vy
    vz
    cB
    cS
    cG
    cK
    c.le
    cV
    glbval.b
    glbval.l
    glbval.g
    glbval.p
    glbva.k
    glbeldm
    biimprd
    mpand
    con3dimp
    wps
    vx
    cB
    riotaund
    syl
    eqtr4d
    pm2.61dan
end
