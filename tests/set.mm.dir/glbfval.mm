include "wcel.mm"
include "cvv.mm"
include "cpw.mm"
include "crio.mm"
include "cmpt.mm"
include "wreu.mm"
include "cab.mm"
include "cres.mm"
include "wceq.mm"
include "elex.mm"
include "cglb.mm"
include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "cbs.mm"
include "cple.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "breqd.mm"
include "ralbidv.mm"
include "imbi12d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "riotaeqbidv.mm"
include "mpteq12dv.mm"
include "reubidv.mm"
include "wb.mm"
include "reueq1.mm"
include "syl.mm"
include "bitrd.mm"
include "abbidv.mm"
include "reseq12d.mm"
include "df-glb.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "mptex.mm"
include "resex.mm"
include "fvmpt.mm"
include "a1i.mm"
include "riotabiia.mm"
include "mpteq2i.mm"
include "reubii.mm"
include "abbii.mm"
include "reseq12i.mm"
include "3eqtr4g.mm"
include "3syl.mm"

theorem glbfval
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cG: class G
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let vs: setvar s
  let vp: setvar p
  assume glbfval.b: |- B = ( Base ` K )
  assume glbfval.l: |- .<_ = ( le ` K )
  assume glbfval.g: |- G = ( glb ` K )
  assume glbfval.p: |- ( ps <-> ( A. y e. s x .<_ y /\ A. z e. B ( A. y e. s z .<_ y -> z .<_ x ) ) )
  assume glbfval.k: |- ( ph -> K e. V )

  disjoint s x
  disjoint s z
  disjoint B s
  disjoint x z
  disjoint B x
  disjoint B z
  disjoint s y
  disjoint K s
  disjoint x y
  disjoint K x
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint p s
  disjoint p x
  disjoint p z
  disjoint B p
  disjoint p y
  disjoint K p
  disjoint .<_ p
  assert |- ( ph -> G = ( ( s e. ~P B |-> ( iota_ x e. B ps ) ) |` { s | E! x e. B ps } ) )

  proof
    wph
    cK
    cV
    wcel
    cK
    cvv
    wcel
    #
    cG
    vs
    cB
    cpw
    #
    wps
    vx
    cB
    crio
    #
    cmpt
    #
    wps
    vx
    cB
    wreu
    #
    vs
    cab
    #
    cres
    #
    wceq
    glbfval.k
    cK
    cV
    elex
    @0
    cK
    cglb
    cfv
    vs
    @1
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
    @8
    c.le
    wbr
    #
    vy
    @10
    wral
    #
    @12
    @7
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
    @18
    vx
    cB
    wreu
    #
    vs
    cab
    #
    cres
    #
    cG
    @6
    vp
    cK
    vs
    vp
    cv
    #
    cbs
    cfv
    #
    cpw
    #
    @7
    @8
    @24
    cple
    cfv
    #
    wbr
    #
    vy
    @10
    wral
    #
    @12
    @8
    @27
    wbr
    #
    vy
    @10
    wral
    #
    @12
    @7
    @27
    wbr
    #
    wi
    #
    vz
    @25
    wral
    #
    wa
    #
    vx
    @25
    crio
    #
    cmpt
    #
    @35
    vx
    @25
    wreu
    #
    vs
    cab
    #
    cres
    @23
    cvv
    cglb
    @24
    cK
    wceq
    #
    @37
    @20
    @39
    @22
    @40
    vs
    @26
    @36
    @1
    @19
    @40
    @25
    cB
    @40
    @25
    cK
    cbs
    cfv
    #
    cB
    @24
    cK
    cbs
    fveq2
    glbfval.b
    syl6eqr
    #
    pweqd
    @40
    @35
    @18
    vx
    @25
    cB
    @42
    @40
    @29
    @11
    @34
    @17
    @40
    @28
    @9
    vy
    @10
    @40
    @27
    c.le
    @7
    @8
    @40
    @27
    cK
    cple
    cfv
    c.le
    @24
    cK
    cple
    fveq2
    glbfval.l
    syl6eqr
    #
    breqd
    ralbidv
    @40
    @33
    @16
    vz
    @25
    cB
    @42
    @40
    @31
    @14
    @32
    @15
    @40
    @30
    @13
    vy
    @10
    @40
    @27
    c.le
    @12
    @8
    @43
    breqd
    ralbidv
    @40
    @27
    c.le
    @12
    @7
    @43
    breqd
    imbi12d
    raleqbidv
    anbi12d
    #
    riotaeqbidv
    mpteq12dv
    @40
    @38
    @21
    vs
    @40
    @38
    @18
    vx
    @25
    wreu
    #
    @21
    @40
    @35
    @18
    vx
    @25
    @44
    reubidv
    @40
    @25
    cB
    wceq
    @45
    @21
    wb
    @42
    @18
    vx
    @25
    cB
    reueq1
    syl
    bitrd
    abbidv
    reseq12d
    vx
    vy
    vz
    vs
    vp
    df-glb
    @20
    @22
    vs
    @1
    @19
    cB
    cB
    @41
    cvv
    glbfval.b
    cK
    cbs
    fvex
    eqeltri
    pwex
    mptex
    resex
    fvmpt
    glbfval.g
    @3
    @20
    @5
    @22
    vs
    @1
    @2
    @19
    wps
    @18
    vx
    cB
    wps
    @18
    wb
    @7
    cB
    wcel
    glbfval.p
    a1i
    riotabiia
    mpteq2i
    @4
    @21
    vs
    wps
    @18
    vx
    cB
    glbfval.p
    reubii
    abbii
    reseq12i
    3eqtr4g
    3syl
end
