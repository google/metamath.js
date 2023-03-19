include "cmnf.mm"
include "cc0.mm"
include "cioo.mm"
include "co.mm"
include "clt.mm"
include "ccnv.mm"
include "gtso.mm"
include "cv.mm"
include "cicc.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cfv.mm"
include "caddc.mm"
include "cmin.mm"
include "cmul.mm"
include "cdiv.mm"
include "dvgt0lem1.mm"
include "eliooord.mm"
include "syl.mm"
include "simprd.mm"
include "cr.mm"
include "wb.mm"
include "wf.mm"
include "ccncf.mm"
include "cncff.mm"
include "ad2antrr.mm"
include "simplrr.mm"
include "ffvelrnd.mm"
include "simplrl.mm"
include "resubcld.mm"
include "0red.mm"
include "wss.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "simpr.mm"
include "posdifd.mm"
include "mpbid.mm"
include "ltdivmul.mm"
include "syl112anc.mm"
include "recnd.mm"
include "mul01d.mm"
include "breqtrd.mm"
include "ltsubaddd.mm"
include "addid2d.mm"
include "fvex.mm"
include "brcnv.mm"
include "sylibr.mm"
include "dvgt0lem2.mm"

theorem dvlt0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cO: class O
  let cS: class S
  let cX: class X
  let cY: class Y
  assume dvgt0.a: |- ( ph -> A e. RR )
  assume dvgt0.b: |- ( ph -> B e. RR )
  assume dvgt0.f: |- ( ph -> F e. ( ( A [,] B ) -cn-> RR ) )
  assume dvlt0.d: |- ( ph -> ( RR _D F ) : ( A (,) B ) --> ( -oo (,) 0 ) )


  assert |- ( ph -> F Isom < , `' < ( ( A [,] B ) , ran F ) )

  proof
    wph
    vx
    vy
    cA
    cB
    cmnf
    cc0
    cioo
    co
    #
    cF
    clt
    ccnv
    #
    dvgt0.a
    dvgt0.b
    dvgt0.f
    dvlt0.d
    gtso
    wph
    vx
    cv
    #
    cA
    cB
    cicc
    co
    #
    wcel
    #
    vy
    cv
    #
    @3
    wcel
    #
    wa
    #
    wa
    #
    @2
    @5
    clt
    wbr
    #
    wa
    #
    @5
    cF
    cfv
    #
    @2
    cF
    cfv
    #
    clt
    wbr
    @12
    @11
    @1
    wbr
    @10
    @11
    cc0
    @12
    caddc
    co
    #
    @12
    clt
    @10
    @11
    @12
    cmin
    co
    #
    cc0
    clt
    wbr
    @11
    @13
    clt
    wbr
    @10
    @14
    @5
    @2
    cmin
    co
    #
    cc0
    cmul
    co
    #
    cc0
    clt
    @10
    @14
    @15
    cdiv
    co
    #
    cc0
    clt
    wbr
    #
    @14
    @16
    clt
    wbr
    #
    @10
    cmnf
    @17
    clt
    wbr
    #
    @18
    @10
    @17
    @0
    wcel
    @20
    @18
    wa
    wph
    cA
    cB
    @0
    cF
    @2
    @5
    dvgt0.a
    dvgt0.b
    dvgt0.f
    dvlt0.d
    dvgt0lem1
    @17
    cmnf
    cc0
    eliooord
    syl
    simprd
    @10
    @14
    cr
    wcel
    cc0
    cr
    wcel
    @15
    cr
    wcel
    cc0
    @15
    clt
    wbr
    #
    @18
    @19
    wb
    @10
    @11
    @12
    @10
    @3
    cr
    @5
    cF
    wph
    @3
    cr
    cF
    wf
    #
    @7
    @9
    wph
    cF
    @3
    cr
    ccncf
    co
    wcel
    @22
    dvgt0.f
    @3
    cr
    cF
    cncff
    syl
    ad2antrr
    #
    wph
    @4
    @6
    @9
    simplrr
    #
    ffvelrnd
    #
    @10
    @3
    cr
    @2
    cF
    @23
    wph
    @4
    @6
    @9
    simplrl
    #
    ffvelrnd
    #
    resubcld
    @10
    0red
    #
    @10
    @5
    @2
    @10
    @3
    cr
    @5
    wph
    @3
    cr
    wss
    #
    @7
    @9
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    @29
    dvgt0.a
    dvgt0.b
    cA
    cB
    iccssre
    syl2anc
    ad2antrr
    #
    @24
    sseldd
    #
    @10
    @3
    cr
    @2
    @30
    @26
    sseldd
    #
    resubcld
    #
    @10
    @9
    @21
    @8
    @9
    simpr
    @10
    @2
    @5
    @32
    @31
    posdifd
    mpbid
    @14
    cc0
    @15
    ltdivmul
    syl112anc
    mpbid
    @10
    @15
    @10
    @15
    @33
    recnd
    mul01d
    breqtrd
    @10
    @11
    @12
    cc0
    @25
    @27
    @28
    ltsubaddd
    mpbid
    @10
    @12
    @10
    @12
    @27
    recnd
    addid2d
    breqtrd
    @12
    @11
    clt
    @2
    cF
    fvex
    @5
    cF
    fvex
    brcnv
    sylibr
    dvgt0lem2
end
