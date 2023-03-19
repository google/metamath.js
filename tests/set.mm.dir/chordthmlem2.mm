include "cmin.mm"
include "co.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "cneg.mm"
include "cpr.mm"
include "wcel.mm"
include "c1.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "rereccld.mm"
include "resubcld.mm"
include "recnd.mm"
include "subcld.mm"
include "cmul.mm"
include "subdird.mm"
include "caddc.mm"
include "2cnd.mm"
include "divcan4d.mm"
include "times2d.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "oveq12d.mm"
include "addcld.mm"
include "divsubdird.mm"
include "pnpcan2d.mm"
include "3eqtr2d.mm"
include "divrec2d.mm"
include "eqtrd.mm"
include "wceq.mm"
include "cc.mm"
include "mulcld.mm"
include "1cnd.mm"
include "eqeltrd.mm"
include "affineequiv.mm"
include "mpbid.mm"
include "halfcld.mm"
include "nnncan1d.mm"
include "3eqtr2rd.mm"
include "subne0d.mm"
include "eqnetrrd.mm"
include "mulne0bbd.mm"
include "subne0ad.mm"
include "necomd.mm"
include "chordthmlem.mm"
include "recne0d.mm"
include "mulne0d.mm"
include "eqnetrd.mm"
include "mulne0bad.mm"
include "divcan5rd.mm"
include "redivcld.mm"
include "angrtmuld.mm"
include "mpbird.mm"

theorem chordthmlem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cF: class F
  let cM: class M
  let cX: class X
  assume chordthmlem2.angdef: |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( Im ` ( log ` ( y / x ) ) ) )
  assume chordthmlem2.A: |- ( ph -> A e. CC )
  assume chordthmlem2.B: |- ( ph -> B e. CC )
  assume chordthmlem2.Q: |- ( ph -> Q e. CC )
  assume chordthmlem2.X: |- ( ph -> X e. RR )
  assume chordthmlem2.M: |- ( ph -> M = ( ( A + B ) / 2 ) )
  assume chordthmlem2.P: |- ( ph -> P = ( ( X x. A ) + ( ( 1 - X ) x. B ) ) )
  assume chordthmlem2.ABequidistQ: |- ( ph -> ( abs ` ( A - Q ) ) = ( abs ` ( B - Q ) ) )
  assume chordthmlem2.PneM: |- ( ph -> P =/= M )
  assume chordthmlem2.QneM: |- ( ph -> Q =/= M )

  disjoint x y
  disjoint Q x
  disjoint Q y
  disjoint P x
  disjoint P y
  disjoint M x
  disjoint M y
  disjoint B x
  disjoint B y
  disjoint A x
  disjoint A y
  assert |- ( ph -> ( ( Q - M ) F ( P - M ) ) e. { ( _pi / 2 ) , -u ( _pi / 2 ) } )

  proof
    wph
    cQ
    cM
    cmin
    co
    #
    cP
    cM
    cmin
    co
    #
    cF
    co
    cpi
    c2
    cdiv
    co
    #
    @2
    cneg
    cpr
    #
    wcel
    @0
    cB
    cM
    cmin
    co
    #
    cF
    co
    @3
    wcel
    wph
    vx
    vy
    cA
    cB
    cQ
    cF
    cM
    chordthmlem2.angdef
    chordthmlem2.A
    chordthmlem2.B
    chordthmlem2.Q
    chordthmlem2.M
    chordthmlem2.ABequidistQ
    wph
    cB
    cA
    wph
    cB
    cA
    chordthmlem2.B
    chordthmlem2.A
    wph
    c1
    c2
    cdiv
    co
    #
    cX
    cmin
    co
    #
    cB
    cA
    cmin
    co
    #
    wph
    @6
    wph
    @5
    cX
    wph
    c2
    c2
    cr
    wcel
    wph
    2re
    a1i
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    #
    rereccld
    #
    chordthmlem2.X
    resubcld
    #
    recnd
    #
    wph
    cB
    cA
    chordthmlem2.B
    chordthmlem2.A
    subcld
    #
    wph
    @1
    @6
    @7
    cmul
    co
    #
    cc0
    wph
    @13
    @5
    @7
    cmul
    co
    #
    cX
    @7
    cmul
    co
    #
    cmin
    co
    @4
    cB
    cP
    cmin
    co
    #
    cmin
    co
    @1
    wph
    @5
    cX
    @7
    wph
    @5
    @9
    recnd
    #
    wph
    cX
    chordthmlem2.X
    recnd
    #
    @12
    subdird
    wph
    @4
    @14
    @16
    @15
    cmin
    wph
    @4
    @7
    c2
    cdiv
    co
    #
    @14
    wph
    @4
    cB
    cB
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cA
    cB
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cmin
    co
    @20
    @22
    cmin
    co
    #
    c2
    cdiv
    co
    @19
    wph
    cB
    @21
    cM
    @23
    cmin
    wph
    cB
    c2
    cmul
    co
    #
    c2
    cdiv
    co
    cB
    @21
    wph
    cB
    c2
    chordthmlem2.B
    wph
    2cnd
    #
    @8
    divcan4d
    wph
    @25
    @20
    c2
    cdiv
    wph
    cB
    chordthmlem2.B
    times2d
    oveq1d
    eqtr3d
    chordthmlem2.M
    oveq12d
    wph
    @20
    @22
    c2
    wph
    cB
    cB
    chordthmlem2.B
    chordthmlem2.B
    addcld
    wph
    cA
    cB
    chordthmlem2.A
    chordthmlem2.B
    addcld
    #
    @26
    @8
    divsubdird
    wph
    @24
    @7
    c2
    cdiv
    wph
    cB
    cA
    cB
    chordthmlem2.B
    chordthmlem2.A
    chordthmlem2.B
    pnpcan2d
    oveq1d
    3eqtr2d
    wph
    @7
    c2
    @12
    @26
    @8
    divrec2d
    eqtrd
    #
    wph
    cP
    cX
    cA
    cmul
    co
    #
    c1
    cX
    cmin
    co
    #
    cB
    cmul
    co
    #
    caddc
    co
    #
    wceq
    @16
    @15
    wceq
    chordthmlem2.P
    wph
    cA
    cP
    cB
    cX
    chordthmlem2.A
    wph
    cP
    @32
    cc
    chordthmlem2.P
    wph
    @29
    @31
    wph
    cX
    cA
    @18
    chordthmlem2.A
    mulcld
    wph
    @30
    cB
    wph
    c1
    cX
    wph
    1cnd
    @18
    subcld
    chordthmlem2.B
    mulcld
    addcld
    eqeltrd
    #
    chordthmlem2.B
    @18
    affineequiv
    mpbid
    oveq12d
    wph
    cB
    cM
    cP
    chordthmlem2.B
    wph
    cM
    @23
    cc
    chordthmlem2.M
    wph
    @22
    @27
    halfcld
    eqeltrd
    #
    @33
    nnncan1d
    3eqtr2rd
    #
    wph
    cP
    cM
    @33
    @34
    chordthmlem2.PneM
    subne0d
    #
    eqnetrrd
    #
    mulne0bbd
    #
    subne0ad
    necomd
    chordthmlem2.QneM
    chordthmlem
    wph
    vx
    vy
    cF
    @0
    @1
    @4
    chordthmlem2.angdef
    wph
    cQ
    cM
    chordthmlem2.Q
    @34
    subcld
    wph
    cP
    cM
    @33
    @34
    subcld
    wph
    cB
    cM
    chordthmlem2.B
    @34
    subcld
    wph
    cQ
    cM
    chordthmlem2.Q
    @34
    chordthmlem2.QneM
    subne0d
    @36
    wph
    @4
    @14
    cc0
    @28
    wph
    @5
    @7
    @17
    @12
    wph
    c2
    @26
    @8
    recne0d
    @38
    mulne0d
    eqnetrd
    wph
    @4
    @1
    cdiv
    co
    #
    @5
    @6
    cdiv
    co
    #
    cr
    wph
    @39
    @14
    @13
    cdiv
    co
    @40
    wph
    @4
    @14
    @1
    @13
    cdiv
    @28
    @35
    oveq12d
    wph
    @5
    @6
    @7
    @17
    @11
    @12
    wph
    @6
    @7
    @11
    @12
    @37
    mulne0bad
    #
    @38
    divcan5rd
    eqtrd
    wph
    @5
    @6
    @9
    @10
    @41
    redivcld
    eqeltrd
    angrtmuld
    mpbird
end
