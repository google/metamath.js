include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "cexp.mm"
include "cmul.mm"
include "addcld.mm"
include "halfcld.mm"
include "subcld.mm"
include "abscld.mm"
include "recnd.mm"
include "sqcld.mm"
include "c1.mm"
include "cc.mm"
include "cc0.mm"
include "cicc.mm"
include "cr.mm"
include "unitssre.mm"
include "sseldi.mm"
include "mulcld.mm"
include "1cnd.mm"
include "eqeltrd.mm"
include "pnpcand.mm"
include "0red.mm"
include "eqidd.mm"
include "mul02d.mm"
include "subid1d.mm"
include "oveq1d.mm"
include "mulid2d.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "addid2d.mm"
include "eqtr2d.mm"
include "chordthmlem3.mm"
include "chordthmlem4.mm"
include "3eqtr4rd.mm"

theorem chordthmlem5
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cX: class X
  assume chordthmlem5.A: |- ( ph -> A e. CC )
  assume chordthmlem5.B: |- ( ph -> B e. CC )
  assume chordthmlem5.Q: |- ( ph -> Q e. CC )
  assume chordthmlem5.X: |- ( ph -> X e. ( 0 [,] 1 ) )
  assume chordthmlem5.P: |- ( ph -> P = ( ( X x. A ) + ( ( 1 - X ) x. B ) ) )
  assume chordthmlem5.ABequidistQ: |- ( ph -> ( abs ` ( A - Q ) ) = ( abs ` ( B - Q ) ) )


  assert |- ( ph -> ( ( abs ` ( P - A ) ) x. ( abs ` ( P - B ) ) ) = ( ( ( abs ` ( B - Q ) ) ^ 2 ) - ( ( abs ` ( P - Q ) ) ^ 2 ) ) )

  proof
    wph
    cQ
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
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    cB
    @1
    cmin
    co
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    @4
    cP
    @1
    cmin
    co
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    cmin
    co
    @7
    @11
    cmin
    co
    cB
    cQ
    cmin
    co
    cabs
    cfv
    c2
    cexp
    co
    #
    cP
    cQ
    cmin
    co
    cabs
    cfv
    c2
    cexp
    co
    #
    cmin
    co
    cP
    cA
    cmin
    co
    cabs
    cfv
    cP
    cB
    cmin
    co
    cabs
    cfv
    cmul
    co
    wph
    @4
    @7
    @11
    wph
    @3
    wph
    @3
    wph
    @2
    wph
    cQ
    @1
    chordthmlem5.Q
    wph
    @0
    wph
    cA
    cB
    chordthmlem5.A
    chordthmlem5.B
    addcld
    halfcld
    #
    subcld
    abscld
    recnd
    sqcld
    wph
    @6
    wph
    @6
    wph
    @5
    wph
    cB
    @1
    chordthmlem5.B
    @15
    subcld
    abscld
    recnd
    sqcld
    wph
    @10
    wph
    @10
    wph
    @9
    wph
    cP
    @1
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
    cc
    chordthmlem5.P
    wph
    @16
    @18
    wph
    cX
    cA
    wph
    cX
    wph
    cc0
    c1
    cicc
    co
    cr
    cX
    unitssre
    chordthmlem5.X
    sseldi
    #
    recnd
    #
    chordthmlem5.A
    mulcld
    wph
    @17
    cB
    wph
    c1
    cX
    wph
    1cnd
    #
    @20
    subcld
    chordthmlem5.B
    mulcld
    addcld
    eqeltrd
    @15
    subcld
    abscld
    recnd
    sqcld
    pnpcand
    wph
    @13
    @8
    @14
    @12
    cmin
    wph
    cA
    cB
    cB
    cQ
    @1
    cc0
    chordthmlem5.A
    chordthmlem5.B
    chordthmlem5.Q
    wph
    0red
    wph
    @1
    eqidd
    #
    wph
    cc0
    cA
    cmul
    co
    #
    c1
    cc0
    cmin
    co
    #
    cB
    cmul
    co
    #
    caddc
    co
    cc0
    cB
    caddc
    co
    cB
    wph
    @23
    cc0
    @25
    cB
    caddc
    wph
    cA
    chordthmlem5.A
    mul02d
    wph
    @25
    c1
    cB
    cmul
    co
    cB
    wph
    @24
    c1
    cB
    cmul
    wph
    c1
    @21
    subid1d
    oveq1d
    wph
    cB
    chordthmlem5.B
    mulid2d
    eqtrd
    oveq12d
    wph
    cB
    chordthmlem5.B
    addid2d
    eqtr2d
    chordthmlem5.ABequidistQ
    chordthmlem3
    wph
    cA
    cB
    cP
    cQ
    @1
    cX
    chordthmlem5.A
    chordthmlem5.B
    chordthmlem5.Q
    @19
    @22
    chordthmlem5.P
    chordthmlem5.ABequidistQ
    chordthmlem3
    oveq12d
    wph
    cA
    cB
    cP
    @1
    cX
    chordthmlem5.A
    chordthmlem5.B
    chordthmlem5.X
    @22
    chordthmlem5.P
    chordthmlem4
    3eqtr4rd
end
