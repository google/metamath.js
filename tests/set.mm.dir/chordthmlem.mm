include "cmin.mm"
include "co.mm"
include "ccos.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "cneg.mm"
include "cpr.mm"
include "wcel.mm"
include "cioc.mm"
include "cr.mm"
include "negpitopissre.mm"
include "caddc.mm"
include "cc.mm"
include "addcld.mm"
include "halfcld.mm"
include "eqeltrd.mm"
include "subcld.mm"
include "subne0d.mm"
include "cmul.mm"
include "oveq1d.mm"
include "times2d.mm"
include "2cnd.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "divcan1d.mm"
include "3eqtr3d.mm"
include "addneintr2d.mm"
include "eqnetrd.mm"
include "neneqd.mm"
include "oveq12.mm"
include "anidms.mm"
include "nsyl.mm"
include "neqned.mm"
include "necomd.mm"
include "angcld.mm"
include "sseldi.mm"
include "recnd.mm"
include "coscld.mm"
include "negsubdi2d.mm"
include "addsubeq4d.mm"
include "mpbid.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "cosangneg2d.mm"
include "addneintrd.mm"
include "neeqtrrd.mm"
include "cabs.mm"
include "eqidd.mm"
include "absnegd.mm"
include "ssscongptld.mm"
include "3eqtr3rd.mm"
include "eqnegad.mm"
include "wb.mm"
include "coseq0negpitopi.mm"
include "syl.mm"

theorem chordthmlem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cF: class F
  let cM: class M
  assume chordthmlem.angdef: |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( Im ` ( log ` ( y / x ) ) ) )
  assume chordthmlem.A: |- ( ph -> A e. CC )
  assume chordthmlem.B: |- ( ph -> B e. CC )
  assume chordthmlem.Q: |- ( ph -> Q e. CC )
  assume chordthmlem.M: |- ( ph -> M = ( ( A + B ) / 2 ) )
  assume chordthmlem.ABequidistQ: |- ( ph -> ( abs ` ( A - Q ) ) = ( abs ` ( B - Q ) ) )
  assume chordthmlem.AneB: |- ( ph -> A =/= B )
  assume chordthmlem.QneM: |- ( ph -> Q =/= M )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint M x
  disjoint M y
  disjoint Q x
  disjoint Q y
  assert |- ( ph -> ( ( Q - M ) F ( B - M ) ) e. { ( _pi / 2 ) , -u ( _pi / 2 ) } )

  proof
    wph
    cQ
    cM
    cmin
    co
    #
    cB
    cM
    cmin
    co
    #
    cF
    co
    #
    ccos
    cfv
    #
    cc0
    wceq
    #
    @2
    cpi
    c2
    cdiv
    co
    #
    @5
    cneg
    cpr
    wcel
    #
    wph
    @3
    wph
    @2
    wph
    @2
    wph
    cpi
    cneg
    cpi
    cioc
    co
    #
    cr
    @2
    negpitopissre
    wph
    vx
    vy
    cF
    @0
    @1
    chordthmlem.angdef
    wph
    cQ
    cM
    chordthmlem.Q
    wph
    cM
    cA
    cB
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cc
    chordthmlem.M
    wph
    @8
    wph
    cA
    cB
    chordthmlem.A
    chordthmlem.B
    addcld
    #
    halfcld
    eqeltrd
    #
    subcld
    #
    wph
    cQ
    cM
    chordthmlem.Q
    @11
    chordthmlem.QneM
    subne0d
    #
    wph
    cB
    cM
    chordthmlem.B
    @11
    subcld
    #
    wph
    cB
    cM
    chordthmlem.B
    @11
    wph
    cM
    cB
    wph
    cM
    cB
    wph
    cM
    cM
    caddc
    co
    #
    cB
    cB
    caddc
    co
    #
    wceq
    #
    cM
    cB
    wceq
    #
    wph
    @15
    @16
    wph
    @15
    @8
    @16
    wph
    cM
    c2
    cmul
    co
    @9
    c2
    cmul
    co
    @15
    @8
    wph
    cM
    @9
    c2
    cmul
    chordthmlem.M
    oveq1d
    wph
    cM
    @11
    times2d
    wph
    @8
    c2
    @10
    wph
    2cnd
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    divcan1d
    3eqtr3d
    #
    wph
    cA
    cB
    cB
    chordthmlem.A
    chordthmlem.B
    chordthmlem.B
    chordthmlem.AneB
    addneintr2d
    eqnetrd
    neneqd
    @18
    @17
    cM
    cB
    cM
    cB
    caddc
    oveq12
    anidms
    nsyl
    neqned
    #
    necomd
    subne0d
    #
    angcld
    #
    sseldi
    recnd
    coscld
    wph
    @0
    @1
    cneg
    #
    cF
    co
    #
    ccos
    cfv
    @0
    cA
    cM
    cmin
    co
    #
    cF
    co
    #
    ccos
    cfv
    @3
    cneg
    @3
    wph
    @24
    @26
    ccos
    wph
    @23
    @25
    @0
    cF
    wph
    @23
    cM
    cB
    cmin
    co
    #
    @25
    wph
    cB
    cM
    chordthmlem.B
    @11
    negsubdi2d
    wph
    @15
    @8
    wceq
    @25
    @27
    wceq
    @19
    wph
    cM
    cM
    cA
    cB
    @11
    @11
    chordthmlem.A
    chordthmlem.B
    addsubeq4d
    mpbid
    #
    eqtr4d
    oveq2d
    fveq2d
    wph
    vx
    vy
    cF
    @0
    @1
    chordthmlem.angdef
    @12
    @13
    @14
    @21
    cosangneg2d
    wph
    vx
    vy
    cQ
    cM
    cA
    cQ
    cM
    cF
    cB
    chordthmlem.angdef
    chordthmlem.Q
    @11
    chordthmlem.A
    chordthmlem.Q
    @11
    chordthmlem.B
    chordthmlem.QneM
    wph
    cM
    cA
    wph
    @15
    cA
    cA
    caddc
    co
    #
    wceq
    #
    cM
    cA
    wceq
    #
    wph
    @15
    @29
    wph
    @29
    @15
    wph
    @29
    @8
    @15
    wph
    cA
    cA
    cB
    chordthmlem.A
    chordthmlem.A
    chordthmlem.B
    chordthmlem.AneB
    addneintrd
    @19
    neeqtrrd
    necomd
    neneqd
    @31
    @30
    cM
    cA
    cM
    cA
    caddc
    oveq12
    anidms
    nsyl
    neqned
    chordthmlem.QneM
    @20
    wph
    @0
    cabs
    cfv
    eqidd
    wph
    @25
    cneg
    #
    cabs
    cfv
    @25
    cabs
    cfv
    cM
    cA
    cmin
    co
    #
    cabs
    cfv
    @27
    cabs
    cfv
    wph
    @25
    wph
    cA
    cM
    chordthmlem.A
    @11
    subcld
    absnegd
    wph
    @32
    @33
    cabs
    wph
    cA
    cM
    chordthmlem.A
    @11
    negsubdi2d
    fveq2d
    wph
    @25
    @27
    cabs
    @28
    fveq2d
    3eqtr3d
    chordthmlem.ABequidistQ
    ssscongptld
    3eqtr3rd
    eqnegad
    wph
    @2
    @7
    wcel
    @4
    @6
    wb
    @22
    @2
    coseq0negpitopi
    syl
    mpbid
end
