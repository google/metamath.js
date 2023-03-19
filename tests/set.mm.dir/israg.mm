include "cs3.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c3.mm"
include "wceq.mm"
include "cc0.mm"
include "c2.mm"
include "co.mm"
include "c1.mm"
include "wa.mm"
include "cword.mm"
include "crab.mm"
include "wcel.mm"
include "crag.mm"
include "wb.mm"
include "s3cld.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "fveq12d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "elrab3.mm"
include "syl.mm"
include "cds.mm"
include "cmir.mm"
include "cbs.mm"
include "cvv.mm"
include "cmpt.mm"
include "df-rag.mm"
include "a1i.mm"
include "simpr.mm"
include "syl6eqr.mm"
include "wrdeq.mm"
include "oveqd.mm"
include "eqidd.mm"
include "fveq1d.mm"
include "oveq123d.mm"
include "anbi2d.mm"
include "rabeqbidv.mm"
include "cstrkg.mm"
include "elexd.mm"
include "fvex.mm"
include "eqeltri.mm"
include "wrdexg.mm"
include "ax-mp.mm"
include "rabex.mm"
include "fvmptd.mm"
include "eleq2d.mm"
include "s3fv0.mm"
include "eqcomd.mm"
include "s3fv2.mm"
include "s3fv1.mm"
include "s3len.mm"
include "biantrurd.mm"
include "bitrd.mm"
include "3bitr4d.mm"

theorem israg
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let vg: setvar g
  let vw: setvar w
  assume israg.p: |- P = ( Base ` G )
  assume israg.d: |- .- = ( dist ` G )
  assume israg.i: |- I = ( Itv ` G )
  assume israg.l: |- L = ( LineG ` G )
  assume israg.s: |- S = ( pInvG ` G )
  assume israg.g: |- ( ph -> G e. TarskiG )
  assume israg.a: |- ( ph -> A e. P )
  assume israg.b: |- ( ph -> B e. P )
  assume israg.c: |- ( ph -> C e. P )


  assert |- ( ph -> ( <" A B C "> e. ( raG ` G ) <-> ( A .- C ) = ( A .- ( ( S ` B ) ` C ) ) ) )

  proof
    wph
    cA
    cB
    cC
    cs3
    #
    vw
    cv
    #
    chash
    cfv
    #
    c3
    wceq
    #
    cc0
    @1
    cfv
    #
    c2
    @1
    cfv
    #
    c.mi
    co
    #
    @4
    @5
    c1
    @1
    cfv
    #
    cS
    cfv
    #
    cfv
    #
    c.mi
    co
    #
    wceq
    #
    wa
    #
    vw
    cP
    cword
    #
    crab
    #
    wcel
    #
    @0
    chash
    cfv
    #
    c3
    wceq
    #
    cc0
    @0
    cfv
    #
    c2
    @0
    cfv
    #
    c.mi
    co
    #
    @18
    @19
    c1
    @0
    cfv
    #
    cS
    cfv
    #
    cfv
    #
    c.mi
    co
    #
    wceq
    #
    wa
    #
    @0
    cG
    crag
    cfv
    #
    wcel
    cA
    cC
    c.mi
    co
    #
    cA
    cC
    cB
    cS
    cfv
    #
    cfv
    #
    c.mi
    co
    #
    wceq
    #
    wph
    @0
    @13
    wcel
    @15
    @26
    wb
    wph
    cA
    cB
    cC
    cP
    israg.a
    israg.b
    israg.c
    s3cld
    @12
    @26
    vw
    @0
    @13
    @1
    @0
    wceq
    #
    @3
    @17
    @11
    @25
    @33
    @2
    @16
    c3
    @1
    @0
    chash
    fveq2
    eqeq1d
    @33
    @6
    @20
    @10
    @24
    @33
    @4
    @18
    @5
    @19
    c.mi
    cc0
    @1
    @0
    fveq1
    #
    c2
    @1
    @0
    fveq1
    #
    oveq12d
    @33
    @4
    @18
    @9
    @23
    c.mi
    @34
    @33
    @5
    @19
    @8
    @22
    @33
    @7
    @21
    cS
    c1
    @1
    @0
    fveq1
    fveq2d
    @35
    fveq12d
    oveq12d
    eqeq12d
    anbi12d
    elrab3
    syl
    wph
    @27
    @14
    @0
    wph
    vg
    cG
    @3
    @4
    @5
    vg
    cv
    #
    cds
    cfv
    #
    co
    #
    @4
    @5
    @7
    @36
    cmir
    cfv
    #
    cfv
    #
    cfv
    #
    @37
    co
    #
    wceq
    #
    wa
    #
    vw
    @36
    cbs
    cfv
    #
    cword
    #
    crab
    #
    @14
    cvv
    crag
    cvv
    crag
    vg
    cvv
    @47
    cmpt
    wceq
    wph
    vw
    vg
    df-rag
    a1i
    wph
    @36
    cG
    wceq
    #
    wa
    #
    @44
    @12
    vw
    @46
    @13
    @49
    @45
    cP
    wceq
    @46
    @13
    wceq
    @49
    @45
    cG
    cbs
    cfv
    #
    cP
    @49
    @36
    cG
    cbs
    wph
    @48
    simpr
    #
    fveq2d
    israg.p
    syl6eqr
    @45
    cP
    wrdeq
    syl
    @49
    @43
    @11
    @3
    @49
    @38
    @6
    @42
    @10
    @49
    @37
    c.mi
    @4
    @5
    @49
    @37
    cG
    cds
    cfv
    c.mi
    @49
    @36
    cG
    cds
    @51
    fveq2d
    israg.d
    syl6eqr
    #
    oveqd
    @49
    @4
    @4
    @41
    @9
    @37
    c.mi
    @52
    @49
    @4
    eqidd
    @49
    @5
    @40
    @8
    @49
    @7
    @39
    cS
    @49
    @39
    cG
    cmir
    cfv
    cS
    @49
    @36
    cG
    cmir
    @51
    fveq2d
    israg.s
    syl6eqr
    fveq1d
    fveq1d
    oveq123d
    eqeq12d
    anbi2d
    rabeqbidv
    wph
    cG
    cstrkg
    israg.g
    elexd
    @14
    cvv
    wcel
    wph
    @12
    vw
    @13
    cP
    cvv
    wcel
    @13
    cvv
    wcel
    cP
    @50
    cvv
    israg.p
    cG
    cbs
    fvex
    eqeltri
    cP
    cvv
    wrdexg
    ax-mp
    rabex
    a1i
    fvmptd
    eleq2d
    wph
    @32
    @25
    @26
    wph
    @28
    @20
    @31
    @24
    wph
    cA
    @18
    cC
    @19
    c.mi
    wph
    @18
    cA
    wph
    cA
    cP
    wcel
    @18
    cA
    wceq
    israg.a
    cA
    cB
    cC
    cP
    s3fv0
    syl
    eqcomd
    #
    wph
    @19
    cC
    wph
    cC
    cP
    wcel
    @19
    cC
    wceq
    israg.c
    cA
    cB
    cC
    cP
    s3fv2
    syl
    eqcomd
    #
    oveq12d
    wph
    cA
    @18
    @30
    @23
    c.mi
    @53
    wph
    cC
    @19
    @29
    @22
    wph
    cB
    @21
    cS
    wph
    @21
    cB
    wph
    cB
    cP
    wcel
    @21
    cB
    wceq
    israg.b
    cA
    cB
    cC
    cP
    s3fv1
    syl
    eqcomd
    fveq2d
    @54
    fveq12d
    oveq12d
    eqeq12d
    wph
    @17
    @25
    @17
    wph
    cA
    cB
    cC
    s3len
    a1i
    biantrurd
    bitrd
    3bitr4d
end
