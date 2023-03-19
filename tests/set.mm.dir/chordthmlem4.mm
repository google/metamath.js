include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cmul.mm"
include "c1.mm"
include "c2.mm"
include "cexp.mm"
include "cr.mm"
include "wcel.mm"
include "1re.mm"
include "a1i.mm"
include "cc0.mm"
include "cicc.mm"
include "unitssre.mm"
include "sseldi.mm"
include "resubcld.mm"
include "recnd.mm"
include "abscld.mm"
include "subcld.mm"
include "mul4d.mm"
include "caddc.mm"
include "wceq.mm"
include "cc.mm"
include "mulcld.mm"
include "addcld.mm"
include "eqeltrd.mm"
include "affineequiv2.mm"
include "mpbid.mm"
include "fveq2d.mm"
include "absmuld.mm"
include "eqtrd.mm"
include "abssubd.mm"
include "affineequiv.mm"
include "3eqtrd.mm"
include "oveq12d.mm"
include "sqvald.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "cdiv.mm"
include "halfcld.mm"
include "sqcld.mm"
include "rehalfcld.mm"
include "subdird.mm"
include "subsq.mm"
include "syl2anc.mm"
include "addsubassd.mm"
include "2halvesd.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "nncand.mm"
include "eqtr2d.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "0re.mm"
include "elicc2i.mm"
include "sylib.mm"
include "simp3d.mm"
include "abssubge0d.mm"
include "simp2d.mm"
include "absidd.mm"
include "absresq.mm"
include "syl.mm"
include "2cnd.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan4d.mm"
include "times2d.mm"
include "divsubdird.mm"
include "pnpcan2d.mm"
include "3eqtr2d.mm"
include "divrec2d.mm"
include "clt.mm"
include "halfgt0.mm"
include "ltled.mm"
include "sqmuld.mm"
include "nnncan1d.mm"
include "3eqtr2rd.mm"
include "3eqtr4rd.mm"
include "eqtr4d.mm"

theorem chordthmlem4
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cM: class M
  let cX: class X
  assume chordthmlem4.A: |- ( ph -> A e. CC )
  assume chordthmlem4.B: |- ( ph -> B e. CC )
  assume chordthmlem4.X: |- ( ph -> X e. ( 0 [,] 1 ) )
  assume chordthmlem4.M: |- ( ph -> M = ( ( A + B ) / 2 ) )
  assume chordthmlem4.P: |- ( ph -> P = ( ( X x. A ) + ( ( 1 - X ) x. B ) ) )


  assert |- ( ph -> ( ( abs ` ( P - A ) ) x. ( abs ` ( P - B ) ) ) = ( ( ( abs ` ( B - M ) ) ^ 2 ) - ( ( abs ` ( P - M ) ) ^ 2 ) ) )

  proof
    wph
    cP
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    cP
    cB
    cmin
    co
    cabs
    cfv
    #
    cmul
    co
    #
    c1
    cX
    cmin
    co
    #
    cabs
    cfv
    #
    cX
    cabs
    cfv
    #
    cmul
    co
    #
    cB
    cA
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
    cmul
    co
    #
    cB
    cM
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
    cP
    cM
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
    cmin
    co
    #
    wph
    @5
    @9
    cmul
    co
    #
    @6
    @9
    cmul
    co
    #
    cmul
    co
    @7
    @9
    @9
    cmul
    co
    #
    cmul
    co
    @3
    @11
    wph
    @5
    @9
    @6
    @9
    wph
    @5
    wph
    @4
    wph
    @4
    wph
    c1
    cX
    c1
    cr
    wcel
    wph
    1re
    a1i
    #
    wph
    cc0
    c1
    cicc
    co
    #
    cr
    cX
    unitssre
    chordthmlem4.X
    sseldi
    #
    resubcld
    recnd
    #
    abscld
    recnd
    wph
    @9
    wph
    @8
    wph
    cB
    cA
    chordthmlem4.B
    chordthmlem4.A
    subcld
    #
    abscld
    recnd
    #
    wph
    @6
    wph
    cX
    wph
    cX
    @24
    recnd
    #
    abscld
    recnd
    @27
    mul4d
    wph
    @1
    @19
    @2
    @20
    cmul
    wph
    @1
    @4
    @8
    cmul
    co
    #
    cabs
    cfv
    @19
    wph
    @0
    @29
    cabs
    wph
    cP
    cX
    cA
    cmul
    co
    #
    @4
    cB
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @0
    @29
    wceq
    chordthmlem4.P
    wph
    cA
    cP
    cB
    cX
    chordthmlem4.A
    wph
    cP
    @32
    cc
    chordthmlem4.P
    wph
    @30
    @31
    wph
    cX
    cA
    @28
    chordthmlem4.A
    mulcld
    wph
    @4
    cB
    @25
    chordthmlem4.B
    mulcld
    addcld
    eqeltrd
    #
    chordthmlem4.B
    @28
    affineequiv2
    mpbid
    fveq2d
    wph
    @4
    @8
    @25
    @26
    absmuld
    eqtrd
    wph
    @2
    cB
    cP
    cmin
    co
    #
    cabs
    cfv
    cX
    @8
    cmul
    co
    #
    cabs
    cfv
    @20
    wph
    cP
    cB
    @34
    chordthmlem4.B
    abssubd
    wph
    @35
    @36
    cabs
    wph
    @33
    @35
    @36
    wceq
    chordthmlem4.P
    wph
    cA
    cP
    cB
    cX
    chordthmlem4.A
    @34
    chordthmlem4.B
    @28
    affineequiv
    mpbid
    #
    fveq2d
    wph
    cX
    @8
    @28
    @26
    absmuld
    3eqtrd
    oveq12d
    wph
    @10
    @21
    @7
    cmul
    wph
    @9
    @27
    sqvald
    oveq2d
    3eqtr4d
    wph
    c1
    c2
    cdiv
    co
    #
    c2
    cexp
    co
    #
    @38
    cX
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
    cmin
    co
    #
    @10
    cmul
    co
    @39
    @10
    cmul
    co
    #
    @42
    @10
    cmul
    co
    #
    cmin
    co
    @11
    @18
    wph
    @39
    @42
    @10
    wph
    @38
    wph
    c1
    wph
    c1
    @22
    recnd
    #
    halfcld
    #
    sqcld
    wph
    @41
    wph
    @41
    wph
    @40
    wph
    @40
    wph
    @38
    cX
    wph
    c1
    @22
    rehalfcld
    #
    @24
    resubcld
    #
    recnd
    #
    abscld
    recnd
    #
    sqcld
    wph
    @9
    @27
    sqcld
    subdird
    wph
    @7
    @43
    @10
    cmul
    wph
    @4
    cX
    cmul
    co
    #
    @39
    @40
    c2
    cexp
    co
    #
    cmin
    co
    #
    @7
    @43
    wph
    @54
    @38
    @40
    caddc
    co
    #
    @38
    @40
    cmin
    co
    #
    cmul
    co
    #
    @52
    wph
    @38
    cc
    wcel
    @40
    cc
    wcel
    @54
    @57
    wceq
    @47
    @50
    @38
    @40
    subsq
    syl2anc
    wph
    @55
    @4
    @56
    cX
    cmul
    wph
    @38
    @38
    caddc
    co
    #
    cX
    cmin
    co
    @55
    @4
    wph
    @38
    @38
    cX
    @47
    @47
    @28
    addsubassd
    wph
    @58
    c1
    cX
    cmin
    wph
    c1
    @46
    2halvesd
    oveq1d
    eqtr3d
    wph
    @38
    cX
    @47
    @28
    nncand
    oveq12d
    eqtr2d
    wph
    @5
    @4
    @6
    cX
    cmul
    wph
    cX
    c1
    @24
    @22
    wph
    cX
    cr
    wcel
    #
    cc0
    cX
    cle
    wbr
    #
    cX
    c1
    cle
    wbr
    #
    wph
    cX
    @23
    wcel
    @59
    @60
    @61
    w3a
    chordthmlem4.X
    cc0
    c1
    cX
    0re
    1re
    elicc2i
    sylib
    #
    simp3d
    abssubge0d
    wph
    cX
    @24
    wph
    @59
    @60
    @61
    @62
    simp2d
    absidd
    oveq12d
    wph
    @42
    @53
    @39
    cmin
    wph
    @40
    cr
    wcel
    @42
    @53
    wceq
    @49
    @40
    absresq
    syl
    oveq2d
    3eqtr4d
    oveq1d
    wph
    @14
    @44
    @17
    @45
    cmin
    wph
    @14
    @38
    @9
    cmul
    co
    #
    c2
    cexp
    co
    @44
    wph
    @13
    @63
    c2
    cexp
    wph
    @13
    @38
    @8
    cmul
    co
    #
    cabs
    cfv
    @38
    cabs
    cfv
    #
    @9
    cmul
    co
    @63
    wph
    @12
    @64
    cabs
    wph
    @12
    @8
    c2
    cdiv
    co
    #
    @64
    wph
    @12
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
    @67
    @69
    cmin
    co
    #
    c2
    cdiv
    co
    @66
    wph
    cB
    @68
    cM
    @70
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
    @68
    wph
    cB
    c2
    chordthmlem4.B
    wph
    2cnd
    #
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    #
    divcan4d
    wph
    @72
    @67
    c2
    cdiv
    wph
    cB
    chordthmlem4.B
    times2d
    oveq1d
    eqtr3d
    chordthmlem4.M
    oveq12d
    wph
    @67
    @69
    c2
    wph
    cB
    cB
    chordthmlem4.B
    chordthmlem4.B
    addcld
    wph
    cA
    cB
    chordthmlem4.A
    chordthmlem4.B
    addcld
    #
    @73
    @74
    divsubdird
    wph
    @71
    @8
    c2
    cdiv
    wph
    cB
    cA
    cB
    chordthmlem4.B
    chordthmlem4.A
    chordthmlem4.B
    pnpcan2d
    oveq1d
    3eqtr2d
    wph
    @8
    c2
    @26
    @73
    @74
    divrec2d
    eqtrd
    #
    fveq2d
    wph
    @38
    @8
    @47
    @26
    absmuld
    wph
    @65
    @38
    @9
    cmul
    wph
    @38
    @48
    wph
    cc0
    @38
    cc0
    cr
    wcel
    wph
    0re
    a1i
    @48
    cc0
    @38
    clt
    wbr
    wph
    halfgt0
    a1i
    ltled
    absidd
    oveq1d
    3eqtrd
    oveq1d
    wph
    @38
    @9
    @47
    @27
    sqmuld
    eqtrd
    wph
    @17
    @41
    @9
    cmul
    co
    #
    c2
    cexp
    co
    @45
    wph
    @16
    @77
    c2
    cexp
    wph
    @16
    @40
    @8
    cmul
    co
    #
    cabs
    cfv
    @77
    wph
    @15
    @78
    cabs
    wph
    @78
    @64
    @36
    cmin
    co
    @12
    @35
    cmin
    co
    @15
    wph
    @38
    cX
    @8
    @47
    @28
    @26
    subdird
    wph
    @12
    @64
    @35
    @36
    cmin
    @76
    @37
    oveq12d
    wph
    cB
    cM
    cP
    chordthmlem4.B
    wph
    cM
    @70
    cc
    chordthmlem4.M
    wph
    @69
    @75
    halfcld
    eqeltrd
    @34
    nnncan1d
    3eqtr2rd
    fveq2d
    wph
    @40
    @8
    @50
    @26
    absmuld
    eqtrd
    oveq1d
    wph
    @41
    @9
    @51
    @27
    sqmuld
    eqtrd
    oveq12d
    3eqtr4rd
    eqtr4d
end
