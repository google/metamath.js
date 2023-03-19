include "csslt.mm"
include "wbr.mm"
include "csur.mm"
include "cpw.mm"
include "wcel.mm"
include "csn.mm"
include "cima.mm"
include "cscut.mm"
include "co.mm"
include "cv.mm"
include "cbday.mm"
include "cfv.mm"
include "wa.mm"
include "crab.mm"
include "cint.mm"
include "wceq.mm"
include "crio.mm"
include "cvv.mm"
include "ssltex1.mm"
include "ssltss1.mm"
include "elpwd.mm"
include "cop.mm"
include "df-br.mm"
include "biimpi.mm"
include "wb.mm"
include "ssltex2.mm"
include "elimasng.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "riotaex.mm"
include "breq1.mm"
include "breq2.mm"
include "bi2anan9.mm"
include "rabbidv.mm"
include "imaeq2d.mm"
include "inteqd.mm"
include "eqeq2d.mm"
include "riotaeqbidv.mm"
include "sneq.mm"
include "df-scut.mm"
include "ovmpt2x.mm"
include "mp3an3.mm"

theorem scutval
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint B a
  disjoint B b
  assert |- ( A <<s B -> ( A |s B ) = ( iota_ x e. { y e. No | ( A <<s { y } /\ { y } <<s B ) } ( bday ` x ) = |^| ( bday " { y e. No | ( A <<s { y } /\ { y } <<s B ) } ) ) )

  proof
    cA
    cB
    csslt
    wbr
    #
    cA
    csur
    cpw
    #
    wcel
    #
    cB
    csslt
    cA
    csn
    #
    cima
    #
    wcel
    #
    cA
    cB
    cscut
    co
    vx
    cv
    cbday
    cfv
    #
    cbday
    cA
    vy
    cv
    csn
    #
    csslt
    wbr
    #
    @7
    cB
    csslt
    wbr
    #
    wa
    #
    vy
    csur
    crab
    #
    cima
    #
    cint
    #
    wceq
    #
    vx
    @11
    crio
    #
    wceq
    #
    @0
    cA
    csur
    cvv
    cA
    cB
    ssltex1
    #
    cA
    cB
    ssltss1
    elpwd
    @0
    @5
    cA
    cB
    cop
    csslt
    wcel
    #
    @0
    @18
    cA
    cB
    csslt
    df-br
    biimpi
    @0
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    @5
    @18
    wb
    @17
    cA
    cB
    ssltex2
    csslt
    cA
    cB
    cvv
    cvv
    elimasng
    syl2anc
    mpbird
    @2
    @5
    @15
    cvv
    wcel
    @16
    @14
    vx
    @11
    riotaex
    va
    vb
    cA
    cB
    @1
    csslt
    va
    cv
    #
    csn
    #
    cima
    @6
    cbday
    @19
    @7
    csslt
    wbr
    #
    @7
    vb
    cv
    #
    csslt
    wbr
    #
    wa
    #
    vy
    csur
    crab
    #
    cima
    #
    cint
    #
    wceq
    #
    vx
    @25
    crio
    @15
    cscut
    cvv
    @4
    @19
    cA
    wceq
    #
    @22
    cB
    wceq
    #
    wa
    #
    @28
    @14
    vx
    @25
    @11
    @31
    @24
    @10
    vy
    csur
    @29
    @21
    @8
    @30
    @23
    @9
    @19
    cA
    @7
    csslt
    breq1
    @22
    cB
    @7
    csslt
    breq2
    bi2anan9
    rabbidv
    #
    @31
    @27
    @13
    @6
    @31
    @26
    @12
    @31
    @25
    @11
    cbday
    @32
    imaeq2d
    inteqd
    eqeq2d
    riotaeqbidv
    @29
    @20
    @3
    csslt
    @19
    cA
    sneq
    imaeq2d
    vx
    vy
    va
    vb
    df-scut
    ovmpt2x
    mp3an3
    syl2anc
end
